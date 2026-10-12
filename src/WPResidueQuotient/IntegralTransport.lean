import WPResidueQuotient.ActualConnection
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
Actual coefficient extension from the integral parameter family to its
characteristic-zero family.  Every map below is induced on the polynomial,
Laurent and localized rings.  Injectivity is proved before restricting to
the factorial modules.  Factorials are only mapped as natural numbers;
none is inverted.  Exact-submodule transport supplies quotient descent,
but does not assert injectivity of that quotient map.
-/

namespace WPResidueQuotient.IntegralTransport

noncomputable section
open scoped BigOperators

section Away

variable {A B : Type*} [CommRing A] [CommRing B]

def awayMap (f : A) (g : B) (φ : A →+* B) (hfg : φ f = g) :
    Localization.Away f →+* Localization.Away g :=
  IsLocalization.Away.lift f (g := (algebraMap B (Localization.Away g)).comp φ) (by
    change IsUnit (algebraMap B (Localization.Away g) (φ f))
    rw [hfg]
    exact IsLocalization.Away.algebraMap_isUnit g)

@[simp] theorem awayMap_algebraMap (f : A) (g : B) (φ : A →+* B)
    (hfg : φ f = g) (a : A) :
    awayMap f g φ hfg (algebraMap A (Localization.Away f) a) =
      algebraMap B (Localization.Away g) (φ a) := by
  simp [awayMap]

theorem awayMap_injective [IsDomain B] (f : A) (g : B) (φ : A →+* B)
    (hfg : φ f = g) (hφ : Function.Injective φ) (hg : g ≠ 0) :
    Function.Injective (awayMap f g φ hfg) := by
  rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f)]
  intro a b
  constructor
  · exact congrArg (awayMap f g φ hfg)
  · intro h
    rw [awayMap_algebraMap, awayMap_algebraMap] at h
    have hinj : Function.Injective (algebraMap B (Localization.Away g)) :=
      IsLocalization.injective (Localization.Away g)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
    exact congrArg (algebraMap A (Localization.Away f)) (hφ (hinj h))

@[simp] theorem awayMap_invSelf (f : A) (g : B) (φ : A →+* B) (hfg : φ f = g) :
    awayMap f g φ hfg (IsLocalization.Away.invSelf f) =
      IsLocalization.Away.invSelf g := by
  have h := congrArg (awayMap f g φ hfg)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away f) f)
  rw [map_mul, map_one, awayMap_algebraMap, hfg] at h
  calc
    awayMap f g φ hfg (IsLocalization.Away.invSelf f) =
        awayMap f g φ hfg (IsLocalization.Away.invSelf f) *
          (algebraMap B (Localization.Away g) g * IsLocalization.Away.invSelf g) := by
      rw [IsLocalization.Away.mul_invSelf, mul_one]
    _ = (algebraMap B (Localization.Away g) g *
        awayMap f g φ hfg (IsLocalization.Away.invSelf f)) *
          IsLocalization.Away.invSelf g := by ring
    _ = IsLocalization.Away.invSelf g := by rw [h, one_mul]

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The graph is a ring homomorphism even when the coefficient rings of
the two derivations differ. -/
def transportGraph [Algebra R A] (φ : A →+* B) (D : Derivation R A A) :
    A →+* TrivSqZeroExt B B where
  toFun a := ⟨φ a, φ (D a)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by
    ext
    · change φ (a + b) = φ a + φ b
      exact map_add φ a b
    · change φ (D (a + b)) = φ (D a) + φ (D b)
      simp only [map_add]
  map_mul' a b := by
    ext
    · exact map_mul φ a b
    · change φ (D (a * b)) = φ a * φ (D b) + φ (D a) * φ b
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring

/-- Agreement on the unlocalized source ring determines compatibility on
the actual localization, by equality of square-zero graph maps. -/
theorem away_derivation_transport (f : A) (g : B) (φ : A →+* B) (hfg : φ f = g)
    [Algebra R (Localization.Away f)] [Algebra S (Localization.Away g)]
    (D : Derivation R (Localization.Away f) (Localization.Away f))
    (E : Derivation S (Localization.Away g) (Localization.Away g))
    (h : ∀ a : A, awayMap f g φ hfg (D (algebraMap A (Localization.Away f) a)) =
      E (awayMap f g φ hfg (algebraMap A (Localization.Away f) a)))
    (z : Localization.Away f) :
    awayMap f g φ hfg (D z) = E (awayMap f g φ hfg z) := by
  have he : transportGraph (awayMap f g φ hfg) D =
      (transportGraph (RingHom.id (Localization.Away g)) E).comp
        (awayMap f g φ hfg) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · rfl
    · exact h a
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun he z)

end Away

section Parameter

variable {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)

def polynomialMap : Polynomial K →+* Polynomial L := Polynomial.mapRingHom φ

@[simp] theorem polynomialMap_X : polynomialMap φ Polynomial.X = Polynomial.X := by
  simp [polynomialMap]

@[simp] theorem polynomialMap_C (k : K) :
    polynomialMap φ (Polynomial.C k) = Polynomial.C (φ k) := by
  simp [polynomialMap]

@[simp] theorem polynomialMap_discriminant :
    polynomialMap φ (Parameter.discriminantPolynomial K) =
      Parameter.discriminantPolynomial L := by
  simp [polynomialMap, Parameter.discriminantPolynomial]

@[simp] theorem polynomialMap_denominator :
    polynomialMap φ (Parameter.denominatorPolynomial K) =
      Parameter.denominatorPolynomial L := by
  simp [Parameter.denominatorPolynomial]

def parameterMap : Parameter.ParameterRing K →+* Parameter.ParameterRing L :=
  awayMap (Parameter.denominatorPolynomial K) (Parameter.denominatorPolynomial L)
    (polynomialMap φ) (polynomialMap_denominator φ)

@[simp] theorem parameterMap_polynomial (P : Polynomial K) :
    parameterMap φ (algebraMap (Polynomial K) (Parameter.ParameterRing K) P) =
      algebraMap (Polynomial L) (Parameter.ParameterRing L) (polynomialMap φ P) :=
  awayMap_algebraMap _ _ _ _ P

@[simp] theorem parameterMap_u :
    parameterMap φ (Parameter.u : Parameter.ParameterRing K) = Parameter.u := by
  simp [Parameter.u]

@[simp] theorem parameterMap_scalar (k : K) :
    parameterMap φ (algebraMap K (Parameter.ParameterRing K) k) =
      algebraMap L (Parameter.ParameterRing L) (φ k) := by
  rw [IsScalarTower.algebraMap_apply K (Polynomial K) (Parameter.ParameterRing K),
    parameterMap_polynomial]
  simp only [Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    polynomialMap_C]
  exact (IsScalarTower.algebraMap_apply L (Polynomial L) (Parameter.ParameterRing L)
    (φ k)).symm

@[simp] theorem parameterMap_discriminant :
    parameterMap φ (Parameter.discriminant : Parameter.ParameterRing K) =
      Parameter.discriminant := by
  simp [Parameter.discriminant, map_ofNat]

theorem parameterMap_injective [IsDomain L] (hφ : Function.Injective φ) :
    Function.Injective (parameterMap φ) := by
  apply awayMap_injective _ _ _ _
  · exact Polynomial.map_injective φ hφ
  · exact Parameter.denominatorPolynomial_ne_zero

theorem polynomialMap_euler (P : Polynomial K) :
    polynomialMap φ (Parameter.polynomialEuler P) =
      Parameter.polynomialEuler (polynomialMap φ P) := by
  simp only [Parameter.polynomialEuler_apply, map_mul, polynomialMap_X]
  change Polynomial.X * (Polynomial.derivative P).map φ =
    Polynomial.X * Polynomial.derivative (P.map φ)
  rw [Polynomial.derivative_map]

theorem parameterMap_theta (r : Parameter.ParameterRing K) :
    parameterMap φ (Parameter.theta r) = Parameter.theta (parameterMap φ r) := by
  apply away_derivation_transport
  intro P
  change parameterMap φ
      (Parameter.theta (algebraMap (Polynomial K) (Parameter.ParameterRing K) P)) =
    Parameter.theta (parameterMap φ
      (algebraMap (Polynomial K) (Parameter.ParameterRing K) P))
  simp only [Parameter.theta_polynomial, parameterMap_polynomial]
  change algebraMap (Polynomial L) (Parameter.ParameterRing L)
    (polynomialMap φ (Parameter.polynomialEuler P)) =
      algebraMap (Polynomial L) (Parameter.ParameterRing L)
        (Parameter.polynomialEuler (polynomialMap φ P))
  rw [polynomialMap_euler]

end Parameter

section Actual

variable {R S : Type*} [CommRing R] [CommRing S]
variable (φ : R →+* S) (u : R) (v : S) (hu : φ u = v)

def laurentMap : LaurentPolynomial R →+* LaurentPolynomial S :=
  AddMonoidAlgebra.mapRingHom Exponents φ

@[simp] theorem laurentMap_single (x : Exponents) (r : R) :
    laurentMap φ (AddMonoidAlgebra.single x r) = AddMonoidAlgebra.single x (φ r) := by
  simp [laurentMap]

@[simp] theorem laurentMap_scalar (r : R) :
    laurentMap φ (algebraMap R (LaurentPolynomial R) r) =
      algebraMap S (LaurentPolynomial S) (φ r) := by
  change laurentMap φ (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 (φ r)
  exact laurentMap_single φ 0 r

@[simp] theorem laurentMap_monomial (a : Fin 6 → ℤ) :
    laurentMap φ (laurentMonomial a) = laurentMonomial a := by
  simp [laurentMonomial]

@[simp] theorem laurentMap_vertex (i : Fin 6) :
    laurentMap φ (laurentVertex i) = laurentVertex i := by
  simp [laurentVertex]

include hu in
theorem laurentMap_torusPolynomial : laurentMap φ (torusPolynomial u) = torusPolynomial v := by
  simp only [torusPolynomial, map_sub, map_one, map_mul, laurentMap_scalar,
    hu, map_sum, laurentMap_vertex]

theorem laurentMap_injective (hφ : Function.Injective φ) :
    Function.Injective (laurentMap φ) := by
  intro P Q h
  ext x
  apply hφ
  have hx := congrArg (fun Z : LaurentPolynomial S => Z.coeff x) h
  simpa only [laurentMap, AddMonoidAlgebra.coeff_mapRingHom] using hx

def actualMap : ActualRing u →+* ActualRing v :=
  awayMap (torusPolynomial u) (torusPolynomial v) (laurentMap φ)
    (laurentMap_torusPolynomial φ u v hu)

@[simp] theorem actualMap_laurent (P : LaurentPolynomial R) :
    actualMap φ u v hu (algebraMap (LaurentPolynomial R) (ActualRing u) P) =
      algebraMap (LaurentPolynomial S) (ActualRing v) (laurentMap φ P) :=
  awayMap_algebraMap _ _ _ _ P

@[simp] theorem actualMap_scalar (r : R) :
    actualMap φ u v hu (algebraMap R (ActualRing u) r) =
      algebraMap S (ActualRing v) (φ r) := by
  rw [IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (ActualRing u),
    actualMap_laurent, laurentMap_scalar,
    ← IsScalarTower.algebraMap_apply S (LaurentPolynomial S) (ActualRing v)]

theorem actualMap_smul (r : R) (g : ActualRing u) :
    actualMap φ u v hu (r • g) = φ r • actualMap φ u v hu g := by
  simp only [Algebra.smul_def, map_mul, actualMap_scalar]

theorem actualMap_injective [IsDomain S] (hφ : Function.Injective φ) :
    Function.Injective (actualMap φ u v hu) := by
  apply awayMap_injective _ _ _ _
  · exact laurentMap_injective φ hφ
  · exact torusPolynomial_ne_zero v

@[simp] theorem actualMap_monomial (a : Fin 6 → ℤ) :
    actualMap φ u v hu (actualMonomial u a) = actualMonomial v a := by
  simp [actualMonomial]

@[simp] theorem actualMap_vertex (i : Fin 6) :
    actualMap φ u v hu (actualVertex u i) = actualVertex v i := by
  simp [actualVertex]

@[simp] theorem actualMap_inverseF : actualMap φ u v hu (inverseF u) = inverseF v :=
  awayMap_invSelf _ _ _ _

@[simp] theorem actualMap_factorialPole (n : ℕ) :
    actualMap φ u v hu (factorialPole u n) = factorialPole v n := by
  simp [factorialPole]

@[simp] theorem actualMap_Gamma (m : ℕ) :
    actualMap φ u v hu (Gamma u m) = Gamma v m := by
  simp [Gamma]

@[simp] theorem actualMap_b (i : Fin 6) : actualMap φ u v hu (b u i) = b v i := by
  simp [b]

@[simp] theorem actualMap_numeratorGenerator (a : Fin 6 → ℕ) (n : ℕ) :
    actualMap φ u v hu (numeratorGenerator u a n) = numeratorGenerator v a n := by
  simp [numeratorGenerator]

theorem laurentMap_logarithmic (w : Exponents →+ ℤ) (P : LaurentPolynomial R) :
    laurentMap φ (logarithmicDerivation w P) = logarithmicDerivation w (laurentMap φ P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | single x r => simp [logarithmicDerivation_single]

theorem actualMap_actualD (i : Fin 5) (g : ActualRing u) :
    actualMap φ u v hu (actualD u i g) = actualD v i (actualMap φ u v hu g) := by
  apply away_derivation_transport
  intro P
  change actualMap φ u v hu
      (actualD u i (algebraMap (LaurentPolynomial R) (ActualRing u) P)) =
    actualD v i (actualMap φ u v hu
      (algebraMap (LaurentPolynomial R) (ActualRing u) P))
  simp only [actualD, localizedLogarithmic, extendDerivation_algebraMap, actualMap_laurent]
  rw [laurentMap_logarithmic]

theorem actualMap_preserves_closed {g : ActualRing u} (hg : g ∈ FClosed u) :
    actualMap φ u v hu g ∈ FClosed v := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, n, ha, rfl⟩
      rw [actualMap_numeratorGenerator]
      exact numeratorGenerator_mem_closed v a n ha
  | zero => simp
  | add g h _ _ hg hh =>
      rw [map_add]
      exact (FClosed v).add_mem hg hh
  | smul r g _ hg =>
      rw [actualMap_smul]
      exact (FClosed v).smul_mem (φ r) hg

theorem actualMap_preserves_interior {g : ActualRing u} (hg : g ∈ FInterior u) :
    actualMap φ u v hu g ∈ FInterior v := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨a, n, ha, rfl⟩
      rw [actualMap_numeratorGenerator]
      exact Submodule.subset_span ⟨a, n, ha, rfl⟩
  | zero => simp
  | add g h _ _ hg hh =>
      rw [map_add]
      exact (FInterior v).add_mem hg hh
  | smul r g _ hg =>
      rw [actualMap_smul]
      exact (FInterior v).smul_mem (φ r) hg

def closedMap : FClosed u →ₛₗ[φ] FClosed v where
  toFun g := ⟨actualMap φ u v hu g, actualMap_preserves_closed φ u v hu g.property⟩
  map_add' g h := Subtype.ext (map_add (actualMap φ u v hu)
    (g : ActualRing u) (h : ActualRing u))
  map_smul' r g := Subtype.ext (actualMap_smul φ u v hu r g)

@[simp] theorem closedMap_coe (g : FClosed u) :
    (closedMap φ u v hu g : ActualRing v) = actualMap φ u v hu g := rfl

theorem closedMap_injective [IsDomain S] (hφ : Function.Injective φ) :
    Function.Injective (closedMap φ u v hu) := by
  intro g h he
  apply Subtype.ext
  exact actualMap_injective φ u v hu hφ (congrArg Subtype.val he)

theorem closedMap_DClosed (i : Fin 5) (g : FClosed u) :
    closedMap φ u v hu (DClosed u i g) = DClosed v i (closedMap φ u v hu g) :=
  Subtype.ext (actualMap_actualD φ u v hu i g)

theorem closedMap_preserves_exact {g : FClosed u} (hg : g ∈ exactSubmodule u) :
    closedMap φ u v hu g ∈ exactSubmodule v := by
  change g ∈ ⨆ i : Fin 5, LinearMap.range (DClosed u i) at hg
  refine Submodule.iSup_induction (fun i : Fin 5 => LinearMap.range (DClosed u i))
    (motive := fun x => closedMap φ u v hu x ∈ exactSubmodule v)
    hg ?_ ?_ ?_
  · intro i g hg
    rcases hg with ⟨h, rfl⟩
    rw [closedMap_DClosed]
    exact DClosed_mem_exact v i (closedMap φ u v hu h)
  · simp
  · intro g h hg hh
    rw [map_add]
    exact (exactSubmodule v).add_mem hg hh

/-- Honest descent along the actual derivative-image submodules.  Its
injectivity remains a separate quotient independence obligation. -/
def quotientMap : ClosedResidueQuotient u →ₛₗ[φ] ClosedResidueQuotient v where
  toFun := Quotient.lift (fun g : FClosed u => Submodule.Quotient.mk (closedMap φ u v hu g))
    (by
      intro g h hgh
      apply (Submodule.Quotient.eq (exactSubmodule v)).mpr
      have hn := (Submodule.quotientRel_def (exactSubmodule u)).mp hgh
      have ht := closedMap_preserves_exact φ u v hu hn
      simpa only [map_sub] using ht)
  map_add' x y := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change Submodule.Quotient.mk (closedMap φ u v hu (x + y)) = _
        rw [map_add]
        rfl
  map_smul' r x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (closedMap φ u v hu (r • x)) = _
      rw [map_smulₛₗ]
      rfl

@[simp] theorem quotientMap_mk (g : FClosed u) :
    quotientMap φ u v hu (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (closedMap φ u v hu g) := rfl

end Actual

section Family

variable {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L)

abbrev familyActualMap : ActualConnection.Ambient K →+* ActualConnection.Ambient L :=
  actualMap (parameterMap φ) Parameter.u Parameter.u (parameterMap_u φ)

abbrev familyClosedMap : FClosed (ActualConnection.parameter K) →ₛₗ[parameterMap φ]
    FClosed (ActualConnection.parameter L) :=
  closedMap (parameterMap φ) Parameter.u Parameter.u (parameterMap_u φ)

abbrev familyQuotientMap : ClosedResidueQuotient (ActualConnection.parameter K)
    →ₛₗ[parameterMap φ] ClosedResidueQuotient (ActualConnection.parameter L) :=
  quotientMap (parameterMap φ) Parameter.u Parameter.u (parameterMap_u φ)

theorem familyActualMap_injective [IsDomain L] (hφ : Function.Injective φ) :
    Function.Injective (familyActualMap φ) :=
  actualMap_injective _ _ _ _ (parameterMap_injective φ hφ)

theorem familyClosedMap_injective [IsDomain L] (hφ : Function.Injective φ) :
    Function.Injective (familyClosedMap φ) :=
  closedMap_injective _ _ _ _ (parameterMap_injective φ hφ)

theorem laurentMap_theta (P : LaurentPolynomial (Parameter.ParameterRing K)) :
    laurentMap (parameterMap φ) (ActualConnection.thetaLaurent K P) =
      ActualConnection.thetaLaurent L (laurentMap (parameterMap φ) P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | single x r =>
      simp only [ActualConnection.thetaLaurent_single, laurentMap_single]
      rw [parameterMap_theta]

theorem familyActualMap_theta (g : ActualConnection.Ambient K) :
    familyActualMap φ (ActualConnection.thetaActual K g) =
      ActualConnection.thetaActual L (familyActualMap φ g) := by
  apply away_derivation_transport
  intro P
  change actualMap (parameterMap φ) Parameter.u Parameter.u (parameterMap_u φ)
      (ActualConnection.thetaActual K
        (algebraMap (LaurentPolynomial (Parameter.ParameterRing K))
          (ActualConnection.Ambient K) P)) =
    ActualConnection.thetaActual L
      (actualMap (parameterMap φ) Parameter.u Parameter.u (parameterMap_u φ)
        (algebraMap (LaurentPolynomial (Parameter.ParameterRing K))
          (ActualConnection.Ambient K) P))
  simp only [ActualConnection.thetaActual_polynomial, actualMap_laurent]
  rw [laurentMap_theta]

theorem familyClosedMap_theta (g : FClosed (ActualConnection.parameter K)) :
    familyClosedMap φ (ActualConnection.thetaClosed K g) =
      ActualConnection.thetaClosed L (familyClosedMap φ g) :=
  Subtype.ext (familyActualMap_theta φ g)

theorem familyQuotientMap_theta (g : ClosedResidueQuotient (ActualConnection.parameter K)) :
    familyQuotientMap φ (ActualConnection.quotientTheta K g) =
      ActualConnection.quotientTheta L (familyQuotientMap φ g) := by
  induction g using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [ActualConnection.quotientTheta_mk, quotientMap_mk]
      rw [familyClosedMap_theta]

end Family

section Padic

variable (p : ℕ) [Fact p.Prime]

def padicCoefficientMap : ℤ_[p] →+* ℚ_[p] := algebraMap ℤ_[p] ℚ_[p]

theorem padicCoefficientMap_injective : Function.Injective (padicCoefficientMap p) := by
  intro x y h
  exact Subtype.ext h

def padicParameterMap : Parameter.ParameterRing ℤ_[p] →+* Parameter.ParameterRing ℚ_[p] :=
  parameterMap (padicCoefficientMap p)

theorem padicParameterMap_injective : Function.Injective (padicParameterMap p) :=
  parameterMap_injective _ (padicCoefficientMap_injective p)

def padicActualMap : ActualConnection.Ambient ℤ_[p] →+* ActualConnection.Ambient ℚ_[p] :=
  familyActualMap (padicCoefficientMap p)

theorem padicActualMap_injective : Function.Injective (padicActualMap p) :=
  familyActualMap_injective _ (padicCoefficientMap_injective p)

def padicClosedMap : FClosed (ActualConnection.parameter ℤ_[p]) →ₛₗ[padicParameterMap p]
    FClosed (ActualConnection.parameter ℚ_[p]) := familyClosedMap (padicCoefficientMap p)

theorem padicClosedMap_injective : Function.Injective (padicClosedMap p) :=
  familyClosedMap_injective _ (padicCoefficientMap_injective p)

theorem padicClosedMap_preserves_exact {g : FClosed (ActualConnection.parameter ℤ_[p])}
    (hg : g ∈ exactSubmodule (ActualConnection.parameter ℤ_[p])) :
    padicClosedMap p g ∈ exactSubmodule (ActualConnection.parameter ℚ_[p]) :=
  closedMap_preserves_exact _ _ _ _ hg

def padicQuotientMap : ClosedResidueQuotient (ActualConnection.parameter ℤ_[p])
    →ₛₗ[padicParameterMap p] ClosedResidueQuotient (ActualConnection.parameter ℚ_[p]) :=
  familyQuotientMap (padicCoefficientMap p)

theorem padicActualMap_theta (g : ActualConnection.Ambient ℤ_[p]) :
    padicActualMap p (ActualConnection.thetaActual ℤ_[p] g) =
      ActualConnection.thetaActual ℚ_[p] (padicActualMap p g) :=
  familyActualMap_theta _ g

theorem padicQuotientMap_theta (g : ClosedResidueQuotient (ActualConnection.parameter ℤ_[p])) :
    padicQuotientMap p (ActualConnection.quotientTheta ℤ_[p] g) =
      ActualConnection.quotientTheta ℚ_[p] (padicQuotientMap p g) :=
  familyQuotientMap_theta _ g

end Padic

end
end WPResidueQuotient.IntegralTransport
