import WPResidueQuotient.LocalizationDerivation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
The actual coefficient ring is the localization of `K[X]` at
`X * (1 - (6*X)^6)`.  Inverting this product supplies both required inverses.
The Euler derivation is first constructed on the polynomial ring and then
extended by the proved localization derivation construction.  Specialization
is an actual localization lift of evaluation, with its unit condition proved.
No residue quotient specialization is asserted in this dependency.
-/

namespace WPResidueQuotient.Parameter

noncomputable section

variable {K : Type*} [CommRing K]

def discriminantPolynomial (K : Type*) [CommRing K] : Polynomial K :=
  1 - (6 * Polynomial.X) ^ 6

def denominatorPolynomial (K : Type*) [CommRing K] : Polynomial K :=
  Polynomial.X * discriminantPolynomial K

abbrev ParameterRing (K : Type*) [CommRing K] :=
  Localization.Away (denominatorPolynomial K)

def u : ParameterRing K := algebraMap (Polynomial K) (ParameterRing K) Polynomial.X

def discriminant : ParameterRing K := 1 - (6 * u) ^ 6

theorem map_discriminantPolynomial :
    algebraMap (Polynomial K) (ParameterRing K) (discriminantPolynomial K) = discriminant := by
  simp [discriminantPolynomial, discriminant, u, map_ofNat]

theorem denominatorPolynomial_ne_zero [IsDomain K] : denominatorPolynomial K ≠ 0 := by
  have hd : discriminantPolynomial K ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    simp [discriminantPolynomial] at he
  exact mul_ne_zero Polynomial.X_ne_zero hd

instance [IsDomain K] : IsDomain (ParameterRing K) :=
  Localization.Away.isDomain denominatorPolynomial_ne_zero

theorem polynomial_embedding_injective [IsDomain K] :
    Function.Injective (algebraMap (Polynomial K) (ParameterRing K)) :=
  IsLocalization.injective (ParameterRing K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors denominatorPolynomial_ne_zero)

theorem u_isUnit : IsUnit (u : ParameterRing K) :=
  IsLocalization.Away.isUnit_of_dvd (x := denominatorPolynomial K)
    (S := ParameterRing K) ⟨discriminantPolynomial K, rfl⟩

theorem discriminant_isUnit : IsUnit (discriminant : ParameterRing K) := by
  rw [← map_discriminantPolynomial]
  exact IsLocalization.Away.isUnit_of_dvd (x := denominatorPolynomial K)
    (S := ParameterRing K) ⟨Polynomial.X, mul_comm _ _⟩

def uInverse : ParameterRing K := ↑(u_isUnit (K := K)).unit⁻¹

def discriminantInverse : ParameterRing K := ↑(discriminant_isUnit (K := K)).unit⁻¹

@[simp] theorem u_mul_uInverse : (u : ParameterRing K) * uInverse = 1 :=
  (u_isUnit (K := K)).mul_val_inv

@[simp] theorem uInverse_mul_u : (uInverse : ParameterRing K) * u = 1 :=
  (u_isUnit (K := K)).val_inv_mul

@[simp] theorem discriminant_mul_inverse :
    (discriminant : ParameterRing K) * discriminantInverse = 1 :=
  (discriminant_isUnit (K := K)).mul_val_inv

def polynomialEuler : Derivation K (Polynomial K) (Polynomial K) :=
  Derivation.mk' ((Polynomial.X : Polynomial K) • Polynomial.derivative) (by
    intro P Q
    simp only [LinearMap.smul_apply, Polynomial.derivative_mul, Algebra.smul_def,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring)

@[simp] theorem polynomialEuler_apply (P : Polynomial K) :
    polynomialEuler P = Polynomial.X * Polynomial.derivative P := rfl

def theta : Derivation K (ParameterRing K) (ParameterRing K) :=
  extendDerivation (denominatorPolynomial K) polynomialEuler

@[simp] theorem theta_polynomial (P : Polynomial K) :
    theta (algebraMap (Polynomial K) (ParameterRing K) P) =
      algebraMap (Polynomial K) (ParameterRing K) (Polynomial.X * Polynomial.derivative P) := by
  exact extendDerivation_algebraMap (denominatorPolynomial K) polynomialEuler P

@[simp] theorem theta_u : theta (u : ParameterRing K) = u := by
  simp [u]

theorem polynomialEuler_discriminant :
    polynomialEuler (discriminantPolynomial K) = -6 * (6 * Polynomial.X) ^ 6 := by
  simp [discriminantPolynomial, Polynomial.derivative_pow, Polynomial.C_ofNat]
  ring

theorem theta_discriminant :
    theta (discriminant : ParameterRing K) = -6 * (6 * u) ^ 6 := by
  rw [← map_discriminantPolynomial, theta_polynomial]
  change algebraMap (Polynomial K) (ParameterRing K)
    (polynomialEuler (discriminantPolynomial K)) = _
  rw [polynomialEuler_discriminant]
  simp [u, map_ofNat]

theorem theta_uInverse : theta (uInverse : ParameterRing K) = -uInverse := by
  have h := (theta (K := K)).leibniz_of_mul_eq_one (uInverse_mul_u (K := K))
  rw [theta_u] at h
  have hm : (uInverse : ParameterRing K) ^ 2 * u = uInverse := by
    calc
      uInverse ^ 2 * u = uInverse * (u * uInverse) := by ring
      _ = uInverse := by rw [u_mul_uInverse, mul_one]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, neg_mul, hm] using h

theorem theta_discriminantInverse :
    theta (discriminantInverse : ParameterRing K) =
      6 * (6 * u) ^ 6 * discriminantInverse ^ 2 := by
  have h := (theta (K := K)).leibniz_of_mul_eq_one
    (mul_comm (discriminantInverse : ParameterRing K) discriminant ▸
      (discriminant_mul_inverse (K := K)))
  rw [theta_discriminant] at h
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h]
  ring

def rationalSpecialization : ParameterRing ℚ →+* ℚ :=
  IsLocalization.Away.lift (denominatorPolynomial ℚ)
    (g := Polynomial.evalRingHom (1 / 10 : ℚ)) (by
      apply isUnit_iff_ne_zero.mpr
      norm_num [denominatorPolynomial, discriminantPolynomial, Polynomial.evalRingHom])

@[simp] theorem rationalSpecialization_polynomial (P : Polynomial ℚ) :
    rationalSpecialization (algebraMap (Polynomial ℚ) (ParameterRing ℚ) P) =
      Polynomial.eval (1 / 10 : ℚ) P := by
  simp [rationalSpecialization]

@[simp] theorem rationalSpecialization_u : rationalSpecialization u = 1 / 10 := by
  simp [u]

@[simp] theorem rationalSpecialization_scalar (q : ℚ) :
    rationalSpecialization (algebraMap ℚ (ParameterRing ℚ) q) = q := by
  rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (ParameterRing ℚ)]
  change rationalSpecialization (algebraMap (Polynomial ℚ) (ParameterRing ℚ) (Polynomial.C q)) = q
  rw [rationalSpecialization_polynomial, Polynomial.eval_C]

def rationalSpecializationAlg : ParameterRing ℚ →ₐ[ℚ] ℚ where
  __ := rationalSpecialization
  commutes' := rationalSpecialization_scalar

theorem rationalSpecialization_discriminant :
    rationalSpecialization discriminant = 14896 / 15625 := by
  norm_num [discriminant, map_sub, map_pow, map_mul, map_ofNat]

theorem rationalSpecialization_uInverse : rationalSpecialization uInverse = 10 := by
  have h := congrArg rationalSpecialization (u_mul_uInverse (K := ℚ))
  rw [map_mul, rationalSpecialization_u, map_one] at h
  linarith

theorem rationalSpecialization_discriminantInverse :
    rationalSpecialization discriminantInverse = 15625 / 14896 := by
  have h := congrArg rationalSpecialization (discriminant_mul_inverse (K := ℚ))
  rw [map_mul, rationalSpecialization_discriminant, map_one] at h
  linarith

theorem numerator_factorization : (14896 : ℕ) = 2 ^ 4 * 7 ^ 2 * 19 := by norm_num

section GoodPrime

variable (p : ℕ) [Fact p.Prime]

theorem padic_nat_isUnit (n : ℕ) (hn : ¬ p ∣ n) : IsUnit (n : ℤ_[p]) := by
  apply PadicInt.isUnit_iff.mpr
  apply PadicInt.norm_natCast_eq_one_iff.mpr
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hn

omit [Fact p.Prime] in
theorem not_dvd_small (hp : 7 ≤ p) (n : ℕ) (hpos : 0 < n) (hlt : n < 7) : ¬ p ∣ n := by
  intro h
  have := Nat.le_of_dvd hpos h
  omega

theorem padic_two_unit (hp : 7 ≤ p) : IsUnit (2 : ℤ_[p]) :=
  padic_nat_isUnit p 2 (not_dvd_small p hp 2 (by norm_num) (by norm_num))

theorem padic_five_unit (hp : 7 ≤ p) : IsUnit (5 : ℤ_[p]) :=
  padic_nat_isUnit p 5 (not_dvd_small p hp 5 (by norm_num) (by norm_num))

theorem padic_six_unit (hp : 7 ≤ p) : IsUnit (6 : ℤ_[p]) :=
  padic_nat_isUnit p 6 (not_dvd_small p hp 6 (by norm_num) (by norm_num))

theorem integralParameter_six_unit (hp : 7 ≤ p) :
    IsUnit (6 : ParameterRing ℤ_[p]) := by
  simpa only [map_ofNat] using (padic_six_unit p hp).map
    (algebraMap ℤ_[p] (ParameterRing ℤ_[p]))

theorem padic_ten_unit (hp : 7 ≤ p) : IsUnit (10 : ℤ_[p]) := by
  convert (padic_two_unit p hp).mul (padic_five_unit p hp) using 1
  norm_num

theorem padic_seven_unit (hp7 : p ≠ 7) : IsUnit (7 : ℤ_[p]) := by
  apply padic_nat_isUnit
  intro h
  exact hp7 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h)

theorem padic_nineteen_unit (hp19 : p ≠ 19) : IsUnit (19 : ℤ_[p]) := by
  apply padic_nat_isUnit
  intro h
  exact hp19 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp h)

theorem padic_14896_unit (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    IsUnit (14896 : ℤ_[p]) := by
  convert ((padic_two_unit p hp).pow 4).mul
    (((padic_seven_unit p hp7).pow 2).mul (padic_nineteen_unit p hp19)) using 1
  norm_num

def integralTenth (hp : 7 ≤ p) : ℤ_[p] := ↑(padic_ten_unit p hp).unit⁻¹

@[simp] theorem ten_mul_integralTenth (hp : 7 ≤ p) :
    (10 : ℤ_[p]) * integralTenth p hp = 1 := (padic_ten_unit p hp).mul_val_inv

theorem integralTenth_unit (hp : 7 ≤ p) : IsUnit (integralTenth p hp) :=
  Units.isUnit _

theorem specialized_discriminant_integral_identity (hp : 7 ≤ p) :
    (5 : ℤ_[p]) ^ 6 * (1 - (6 * integralTenth p hp) ^ 6) = 14896 := by
  have h3 : (5 : ℤ_[p]) * (6 * integralTenth p hp) = 3 := by
    calc
      (5 : ℤ_[p]) * (6 * integralTenth p hp) = 3 * (10 * integralTenth p hp) := by ring
      _ = 3 := by rw [ten_mul_integralTenth, mul_one]
  calc
    (5 : ℤ_[p]) ^ 6 * (1 - (6 * integralTenth p hp) ^ 6) =
        (5 : ℤ_[p]) ^ 6 - (5 * (6 * integralTenth p hp)) ^ 6 := by ring
    _ = (5 : ℤ_[p]) ^ 6 - 3 ^ 6 := by rw [h3]
    _ = 14896 := by norm_num

theorem specialized_discriminant_unit (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    IsUnit (1 - (6 * integralTenth p hp) ^ 6 : ℤ_[p]) := by
  have h : IsUnit ((5 : ℤ_[p]) ^ 6 * (1 - (6 * integralTenth p hp) ^ 6)) := by
    rw [specialized_discriminant_integral_identity]
    exact padic_14896_unit p hp hp7 hp19
  exact isUnit_of_mul_isUnit_right h

def integralSpecialization (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    ParameterRing ℤ_[p] →+* ℤ_[p] :=
  IsLocalization.Away.lift (denominatorPolynomial ℤ_[p])
    (g := Polynomial.evalRingHom (integralTenth p hp)) (by
      simpa [denominatorPolynomial, discriminantPolynomial] using
        (integralTenth_unit p hp).mul (specialized_discriminant_unit p hp hp7 hp19))

@[simp] theorem integralSpecialization_polynomial (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)
    (P : Polynomial ℤ_[p]) :
    integralSpecialization p hp hp7 hp19
      (algebraMap (Polynomial ℤ_[p]) (ParameterRing ℤ_[p]) P) =
        Polynomial.eval (integralTenth p hp) P := by
  simp [integralSpecialization]

@[simp] theorem integralSpecialization_u (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    integralSpecialization p hp hp7 hp19 u = integralTenth p hp := by simp [u]

@[simp] theorem integralSpecialization_scalar (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19)
    (r : ℤ_[p]) :
    integralSpecialization p hp hp7 hp19 (algebraMap ℤ_[p] (ParameterRing ℤ_[p]) r) = r := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] (Polynomial ℤ_[p]) (ParameterRing ℤ_[p])]
  change integralSpecialization p hp hp7 hp19
    (algebraMap (Polynomial ℤ_[p]) (ParameterRing ℤ_[p]) (Polynomial.C r)) = r
  rw [integralSpecialization_polynomial, Polynomial.eval_C]

def integralSpecializationAlg (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    ParameterRing ℤ_[p] →ₐ[ℤ_[p]] ℤ_[p] where
  __ := integralSpecialization p hp hp7 hp19
  commutes' := integralSpecialization_scalar p hp hp7 hp19

theorem integralSpecialization_discriminant (hp : 7 ≤ p) (hp7 : p ≠ 7) (hp19 : p ≠ 19) :
    integralSpecialization p hp hp7 hp19 discriminant =
      1 - (6 * integralTenth p hp) ^ 6 := by
  simp [discriminant, map_ofNat]

end GoodPrime

end

end WPResidueQuotient.Parameter
