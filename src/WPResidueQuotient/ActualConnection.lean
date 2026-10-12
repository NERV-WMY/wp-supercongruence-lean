import WPResidueQuotient.ParameterRing
import WPResidueQuotient.ActualModule
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

/-!
The genuine Euler connection acts coefficientwise on the actual Laurent
algebra and extends to the actual localization at `f`.  Its preservation and
descent use actual derivative images in `FClosed`; no free quotient basis is
assumed.  The Gamma and boundary columns are first identities of actual
rational functions.  The corrected boundary class uses the separately proved
finite numerator reduction, explicitly exposed as an equality if needed.
-/

namespace WPResidueQuotient.ActualConnection

noncomputable section
open scoped BigOperators

variable (K : Type*) [CommRing K]

abbrev Coeff := Parameter.ParameterRing K
abbrev parameter : Coeff K := Parameter.u
abbrev Ambient := ActualRing (parameter K)

def thetaLaurentLinear : LaurentPolynomial (Coeff K) →ₗ[K] LaurentPolynomial (Coeff K) :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Parameter.theta (K := K)).toLinearMap).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

@[simp] theorem thetaLaurentLinear_single (x : Exponents) (r : Coeff K) :
    thetaLaurentLinear K (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single x (Parameter.theta r) := by
  simp [thetaLaurentLinear]

theorem thetaLaurentLinear_leibniz (P Q : LaurentPolynomial (Coeff K)) :
    thetaLaurentLinear K (P * Q) =
      P * thetaLaurentLinear K Q + Q * thetaLaurentLinear K P := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
      simp only [add_mul, map_add, hP, hQ, mul_add]
      abel
  | single x r =>
      induction Q using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add P Q hP hQ =>
          simp only [mul_add, map_add, hP, hQ, add_mul]
          abel
      | single y s =>
          simp [AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.single_add,
            Derivation.leibniz, mul_comm]

def thetaLaurent : Derivation K (LaurentPolynomial (Coeff K)) (LaurentPolynomial (Coeff K)) :=
  Derivation.mk' (thetaLaurentLinear K) (by
    intro P Q
    simpa only [smul_eq_mul] using thetaLaurentLinear_leibniz K P Q)

@[simp] theorem thetaLaurent_single (x : Exponents) (r : Coeff K) :
    thetaLaurent K (AddMonoidAlgebra.single x r) =
      AddMonoidAlgebra.single x (Parameter.theta r) :=
  thetaLaurentLinear_single K x r

@[simp] theorem thetaLaurent_scalar (r : Coeff K) :
    thetaLaurent K (algebraMap (Coeff K) (LaurentPolynomial (Coeff K)) r) =
      algebraMap (Coeff K) (LaurentPolynomial (Coeff K)) (Parameter.theta r) :=
  thetaLaurent_single K 0 r

@[simp] theorem thetaLaurent_monomial (a : Fin 6 → ℤ) :
    thetaLaurent K (laurentMonomial (R := Coeff K) a) = 0 := by
  simp [laurentMonomial]

@[simp] theorem thetaLaurent_vertex (i : Fin 6) :
    thetaLaurent K (laurentVertex (R := Coeff K) i) = 0 := by
  simp [laurentVertex]

theorem thetaLaurent_f :
    thetaLaurent K (torusPolynomial (parameter K)) = torusPolynomial (parameter K) - 1 := by
  rw [torusPolynomial, Derivation.map_sub, Derivation.leibniz, thetaLaurent_scalar]
  simp only [Derivation.map_one_eq_zero, Parameter.theta_u, map_sum, thetaLaurent_vertex,
    Finset.sum_const_zero, smul_eq_mul]
  ring

def thetaActual : Derivation K (Ambient K) (Ambient K) :=
  extendDerivation (torusPolynomial (parameter K)) (thetaLaurent K)

@[simp] theorem thetaActual_polynomial (P : LaurentPolynomial (Coeff K)) :
    thetaActual K (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K) P) =
      algebraMap (LaurentPolynomial (Coeff K)) (Ambient K) (thetaLaurent K P) :=
  extendDerivation_algebraMap (torusPolynomial (parameter K)) (thetaLaurent K) P

@[simp] theorem thetaActual_scalar (r : Coeff K) :
    thetaActual K (algebraMap (Coeff K) (Ambient K) r) =
      algebraMap (Coeff K) (Ambient K) (Parameter.theta r) := by
  rw [IsScalarTower.algebraMap_apply (Coeff K) (LaurentPolynomial (Coeff K)) (Ambient K),
    thetaActual_polynomial, thetaLaurent_scalar,
    ← IsScalarTower.algebraMap_apply (Coeff K) (LaurentPolynomial (Coeff K)) (Ambient K)]

theorem thetaActual_smul (r : Coeff K) (g : Ambient K) :
    thetaActual K (r • g) = (Parameter.theta r) • g + r • thetaActual K g := by
  simp only [Algebra.smul_def, Derivation.leibniz, thetaActual_scalar,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

@[simp] theorem thetaActual_monomial (a : Fin 6 → ℤ) :
    thetaActual K (actualMonomial (parameter K) a) = 0 := by
  simp [actualMonomial]

@[simp] theorem thetaActual_vertex (i : Fin 6) :
    thetaActual K (actualVertex (parameter K) i) = 0 := by
  simp [actualVertex]

theorem thetaActual_f :
    thetaActual K (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K)
      (torusPolynomial (parameter K))) =
      algebraMap (LaurentPolynomial (Coeff K)) (Ambient K)
        (torusPolynomial (parameter K)) - 1 := by
  rw [thetaActual_polynomial, thetaLaurent_f, map_sub, map_one]

theorem thetaActual_inverseF :
    thetaActual K (inverseF (parameter K)) =
      inverseF (parameter K) ^ 2 - inverseF (parameter K) := by
  rw [inverseF, derivation_invSelf, thetaActual_f]
  have h := imageF_mul_inverseF (parameter K)
  change -(inverseF (parameter K)) ^ 2 *
    (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K)
      (torusPolynomial (parameter K)) - 1) =
        inverseF (parameter K) ^ 2 - inverseF (parameter K)
  calc
    _ = inverseF (parameter K) ^ 2 - inverseF (parameter K) *
      (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K)
        (torusPolynomial (parameter K)) * inverseF (parameter K)) := by ring
    _ = _ := by rw [h, mul_one]

theorem thetaActual_factorialPole (n : ℕ) :
    thetaActual K (factorialPole (parameter K) n) =
      factorialPole (parameter K) (n + 1) -
        (n + 1 : Ambient K) * factorialPole (parameter K) n := by
  simp only [factorialPole, Derivation.leibniz, Derivation.map_natCast,
    smul_zero, add_zero, Derivation.leibniz_pow, Nat.add_sub_cancel]
  rw [thetaActual_inverseF, Nat.factorial_succ]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  ring

theorem thetaActual_Gamma_succ (n : ℕ) :
    thetaActual K (Gamma (parameter K) (n + 1)) =
      Gamma (parameter K) (n + 2) - (n + 1 : Ambient K) * Gamma (parameter K) (n + 1) := by
  simpa only [show n + 2 = (n + 1) + 1 by omega, Gamma_succ] using
    thetaActual_factorialPole K n

theorem thetaActual_boundary (i : Fin 6) :
    thetaActual K (b (parameter K) i) =
      actualVertex (parameter K) i * Gamma (parameter K) 2 - b (parameter K) i := by
  rw [b, Derivation.leibniz, thetaActual_vertex, smul_zero, add_zero, thetaActual_inverseF]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply,
    Gamma, Nat.reduceSub, Nat.factorial_one, Nat.cast_one, one_mul]
  ring

theorem thetaActual_numeratorGenerator (a : Fin 6 → ℕ) (n : ℕ) :
    thetaActual K (numeratorGenerator (parameter K) a n) =
      numeratorGenerator (parameter K) a (n + 1) -
        (n + 1 : Ambient K) * numeratorGenerator (parameter K) a n := by
  rw [numeratorGenerator, Derivation.leibniz, thetaActual_monomial,
    smul_zero, add_zero, thetaActual_factorialPole]
  simp only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, numeratorGenerator]
  ring

theorem thetaActual_preserves_closed {g : Ambient K} (hg : g ∈ FClosed (parameter K)) :
    thetaActual K g ∈ FClosed (parameter K) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, n, ha, rfl⟩ := hg
      rw [thetaActual_numeratorGenerator]
      apply (FClosed (parameter K)).sub_mem
      · exact numeratorGenerator_mem_closed (parameter K) a (n + 1) (by omega)
      · simpa only [Algebra.smul_def, map_natCast, map_add, map_one] using
          (FClosed (parameter K)).smul_mem (n + 1 : Coeff K)
            (numeratorGenerator_mem_closed (parameter K) a n ha)
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (FClosed (parameter K)).add_mem ihx ihy
  | smul r x hx ih =>
      rw [thetaActual_smul]
      exact (FClosed (parameter K)).add_mem
        ((FClosed (parameter K)).smul_mem _ hx) ((FClosed (parameter K)).smul_mem _ ih)

def thetaClosed : FClosed (parameter K) →ₗ[K] FClosed (parameter K) where
  toFun g := ⟨thetaActual K g, thetaActual_preserves_closed K g.property⟩
  map_add' g h := Subtype.ext (map_add (thetaActual K) (g : Ambient K) (h : Ambient K))
  map_smul' k g := Subtype.ext (Derivation.map_smul (thetaActual K) k (g : Ambient K))

theorem thetaClosed_smul (r : Coeff K) (g : FClosed (parameter K)) :
    thetaClosed K (r • g) = (Parameter.theta r) • g + r • thetaClosed K g :=
  Subtype.ext (thetaActual_smul K r g)

theorem thetaLaurent_commutes_logarithmic (w : Exponents →+ ℤ)
    (P : LaurentPolynomial (Coeff K)) :
    thetaLaurent K (logarithmicDerivation w P) =
      logarithmicDerivation w (thetaLaurent K P) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | single x r =>
    simp [logarithmicDerivation_single, Derivation.leibniz, smul_eq_mul]

section LocalizationExt

variable {S A B : Type*} [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S B] [Algebra A B]

/-- Localization uniqueness for actual derivations, obtained from their
square-zero graph ring homomorphisms. -/
theorem derivation_localization_ext (f : A) [IsLocalization.Away f B]
    (D E : Derivation S B B)
    (h : ∀ a : A, D (algebraMap A B a) = E (algebraMap A B a)) : D = E := by
  have hg : (derivationGraph (B := B) D).toRingHom =
      (derivationGraph (B := B) E).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · rfl
    · exact h a
  apply Derivation.ext
  intro b
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hg b)

end LocalizationExt

theorem thetaActual_commutes_logarithmic (i : Fin 5) (g : Ambient K) :
    thetaActual K (actualD (parameter K) i g) =
      actualD (parameter K) i (thetaActual K g) := by
  let D : Derivation K (Ambient K) (Ambient K) :=
    (actualD (parameter K) i).restrictScalars K
  have hzero : ⁅thetaActual K, D⁆ = 0 := by
    apply derivation_localization_ext (torusPolynomial (parameter K))
    intro P
    rw [Derivation.commutator_apply]
    change thetaActual K (actualD (parameter K) i
      (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K) P)) -
        actualD (parameter K) i (thetaActual K
          (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K) P)) = 0
    simp only [actualD, localizedLogarithmic, extendDerivation_algebraMap,
      thetaActual_polynomial]
    apply sub_eq_zero.mpr
    exact congrArg (algebraMap (LaurentPolynomial (Coeff K)) (Ambient K))
      (thetaLaurent_commutes_logarithmic K (coordinateWeight i) P)
  have h := DFunLike.congr_fun hzero g
  change thetaActual K (actualD (parameter K) i g) -
    actualD (parameter K) i (thetaActual K g) = 0 at h
  exact sub_eq_zero.mp h

theorem thetaClosed_commutes_DClosed (i : Fin 5) (g : FClosed (parameter K)) :
    thetaClosed K (DClosed (parameter K) i g) =
      DClosed (parameter K) i (thetaClosed K g) :=
  Subtype.ext (thetaActual_commutes_logarithmic K i g)

theorem thetaClosed_preserves_exact {g : FClosed (parameter K)}
    (hg : g ∈ exactSubmodule (parameter K)) :
    thetaClosed K g ∈ exactSubmodule (parameter K) := by
  change g ∈ ⨆ i : Fin 5, LinearMap.range (DClosed (parameter K) i) at hg
  refine Submodule.iSup_induction (fun i : Fin 5 => LinearMap.range (DClosed (parameter K) i))
    (motive := fun x => thetaClosed K x ∈ exactSubmodule (parameter K))
    hg ?_ ?_ ?_
  · intro i g hg
    rcases hg with ⟨h, rfl⟩
    rw [thetaClosed_commutes_DClosed]
    exact DClosed_mem_exact (parameter K) i (thetaClosed K h)
  · simp
  · intro g h hg hh
    rw [map_add]
    exact (exactSubmodule (parameter K)).add_mem hg hh

/-- Descent is a `K`-linear map on the actual `R`-module quotient, with the
parameter Leibniz rule below.  It is not falsely declared `R`-linear. -/
def quotientTheta : ClosedResidueQuotient (parameter K) →ₗ[K]
    ClosedResidueQuotient (parameter K) where
  toFun := Quotient.lift (fun g : FClosed (parameter K) =>
    Submodule.Quotient.mk (thetaClosed K g)) (by
      intro g h hgh
      apply (Submodule.Quotient.eq (exactSubmodule (parameter K))).mpr
      have hn := (Submodule.quotientRel_def (exactSubmodule (parameter K))).mp hgh
      have ht := thetaClosed_preserves_exact K hn
      simpa only [map_sub] using ht)
  map_add' x y := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change Submodule.Quotient.mk (thetaClosed K (x + y)) = _
        rw [map_add]
        rfl
  map_smul' k x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (thetaClosed K (k • x)) = _
      rw [map_smul]
      rfl

@[simp] theorem quotientTheta_mk (g : FClosed (parameter K)) :
    quotientTheta K (Submodule.Quotient.mk g) = Submodule.Quotient.mk (thetaClosed K g) := rfl

theorem quotientTheta_smul (r : Coeff K) (x : ClosedResidueQuotient (parameter K)) :
    quotientTheta K (r • x) = (Parameter.theta r) • x + r • quotientTheta K x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (thetaClosed K (r • x)) = _
    rw [thetaClosed_smul]
    rfl

def gammaClosed (n : ℕ) : FClosed (parameter K) :=
  ⟨Gamma (parameter K) (n + 1), by
    rw [Gamma_succ]
    exact FInterior_le_FClosed (parameter K) (factorialPole_mem_interior (parameter K) n)⟩

def qGamma (n : ℕ) : ClosedResidueQuotient (parameter K) :=
  Submodule.Quotient.mk (gammaClosed K n)

theorem thetaClosed_gammaClosed (n : ℕ) :
    thetaClosed K (gammaClosed K n) = gammaClosed K (n + 1) - (n + 1) • gammaClosed K n := by
  apply Subtype.ext
  change thetaActual K (Gamma (parameter K) (n + 1)) =
    Gamma (parameter K) ((n + 1) + 1) - (n + 1) • Gamma (parameter K) (n + 1)
  simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    show n + 1 + 1 = n + 2 by omega] using thetaActual_Gamma_succ K n

theorem quotientTheta_Gamma (n : ℕ) :
    quotientTheta K (qGamma K n) = qGamma K (n + 1) - (n + 1) • qGamma K n := by
  change Submodule.Quotient.mk (thetaClosed K (gammaClosed K n)) = _
  rw [thetaClosed_gammaClosed]
  rfl

@[simp] theorem actualMonomial_zero :
    actualMonomial (parameter K) (fun _ : Fin 6 => (0 : ℤ)) = 1 := by
  have h : sixToFive (fun _ : Fin 6 => (0 : ℤ)) = 0 := by
    ext i
    simp [sixToFive]
  simp [actualMonomial, laurentMonomial, h, ← AddMonoidAlgebra.one_def]

theorem boundary_mem_closed (i : Fin 6) : b (parameter K) i ∈ FClosed (parameter K) := by
  have h := numeratorGenerator_mem_closed (parameter K)
    (addNumeratorExponent (fun _ => 0) i) 0 (by rw [addNumeratorExponent_sum]; simp)
  rw [numeratorGenerator_add] at h
  simpa [factorialPole, b] using h

theorem vertex_GammaTwo_mem_closed (i : Fin 6) :
    actualVertex (parameter K) i * Gamma (parameter K) 2 ∈ FClosed (parameter K) := by
  have h := numeratorGenerator_mem_closed (parameter K)
    (addNumeratorExponent (fun _ => 0) i) 1 (by rw [addNumeratorExponent_sum]; simp)
  rw [numeratorGenerator_add] at h
  simpa [factorialPole, Gamma] using h

def boundaryClosed (i : Fin 6) : FClosed (parameter K) :=
  ⟨b (parameter K) i, boundary_mem_closed K i⟩

def vertexGammaTwoClosed (i : Fin 6) : FClosed (parameter K) :=
  ⟨actualVertex (parameter K) i * Gamma (parameter K) 2, vertex_GammaTwo_mem_closed K i⟩

def qBoundary (i : Fin 6) : ClosedResidueQuotient (parameter K) :=
  Submodule.Quotient.mk (boundaryClosed K i)

def qVertexGammaTwo (i : Fin 6) : ClosedResidueQuotient (parameter K) :=
  Submodule.Quotient.mk (vertexGammaTwoClosed K i)

theorem thetaClosed_boundaryClosed (i : Fin 6) :
    thetaClosed K (boundaryClosed K i) = vertexGammaTwoClosed K i - boundaryClosed K i :=
  Subtype.ext (thetaActual_boundary K i)

theorem quotientTheta_boundary (i : Fin 6) :
    quotientTheta K (qBoundary K i) = qVertexGammaTwo K i - qBoundary K i := by
  change Submodule.Quotient.mk (thetaClosed K (boundaryClosed K i)) = _
  rw [thetaClosed_boundaryClosed]
  rfl

/-- The actual inverse of `6u`, with the only coefficient-unit premise
explicit.  This premise is proved in the rational and good-prime rings. -/
def boundaryScalar (h6 : IsUnit (6 : K)) : Coeff K :=
  algebraMap K (Coeff K) ↑h6.unit⁻¹ * Parameter.uInverse

theorem six_parameter_mul_boundaryScalar (h6 : IsUnit (6 : K)) :
    (6 * parameter K) * boundaryScalar K h6 = 1 := by
  have hc : (6 : Coeff K) * algebraMap K (Coeff K) ↑h6.unit⁻¹ = 1 := by
    have h := congrArg (algebraMap K (Coeff K)) h6.mul_val_inv
    simpa only [map_mul, map_ofNat, map_one] using h
  calc
    (6 * parameter K) * boundaryScalar K h6 =
      (6 * algebraMap K (Coeff K) ↑h6.unit⁻¹) *
        ((parameter K) * Parameter.uInverse) := by unfold boundaryScalar; ring
    _ = 1 := by rw [hc, Parameter.u_mul_uInverse, one_mul]

theorem theta_boundaryScalar (h6 : IsUnit (6 : K)) :
    Parameter.theta (boundaryScalar K h6) = -boundaryScalar K h6 := by
  simp [boundaryScalar, Derivation.leibniz, Parameter.theta_uInverse, smul_eq_mul]

def correctedBoundary (h6 : IsUnit (6 : K)) (i : Fin 6) :
    ClosedResidueQuotient (parameter K) :=
  qBoundary K i - boundaryScalar K h6 • qGamma K 0

/-- The finite numerator reduction is the sole outstanding input for this
boundary column.  Both sides are classes of the actual rational functions.
No independence or quotient basis is assumed here. -/
theorem quotientTheta_correctedBoundary (h6 : IsUnit (6 : K)) (i : Fin 6)
    (hred : qVertexGammaTwo K i = boundaryScalar K h6 • (qGamma K 1 - qGamma K 0)) :
    quotientTheta K (correctedBoundary K h6 i) = -correctedBoundary K h6 i := by
  rw [correctedBoundary, map_sub, quotientTheta_boundary, quotientTheta_smul,
    theta_boundaryScalar, quotientTheta_Gamma, hred]
  simp only [Nat.zero_add, one_smul, smul_sub, neg_smul]
  abel

end

end WPResidueQuotient.ActualConnection
