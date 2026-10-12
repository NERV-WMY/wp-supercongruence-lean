import WPResidueQuotient.VertexExact
import WPResidueQuotient.ParameterRing

/-!
Coefficient change on the actual Laurent algebra, localization and factorial
modules. All formulas are localization identities; no formal-series value or
residue basis is used.
-/

namespace WPResidueQuotient.Specialization

noncomputable section

open scoped BigOperators

variable {R S : Type*} [CommRing R] [CommRing S]

def laurentMap (φ : R →+* S) : LaurentPolynomial R →+* LaurentPolynomial S :=
  AddMonoidAlgebra.mapRingHom Exponents φ

@[simp] theorem laurentMap_single (φ : R →+* S) (x : Exponents) (r : R) :
    laurentMap φ (AddMonoidAlgebra.single x r) = AddMonoidAlgebra.single x (φ r) :=
  AddMonoidAlgebra.mapRingHom_single φ x r

@[simp] theorem laurentMap_coefficient (φ : R →+* S) (P : LaurentPolynomial R)
    (x : Exponents) : (laurentMap φ P).coeff x = φ (P.coeff x) :=
  AddMonoidAlgebra.coeff_mapRingHom φ P x

@[simp] theorem laurentMap_scalar (φ : R →+* S) (r : R) :
    laurentMap φ (algebraMap R (LaurentPolynomial R) r) =
      algebraMap S (LaurentPolynomial S) (φ r) := by
  change laurentMap φ (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 (φ r)
  exact laurentMap_single φ 0 r

theorem laurentMap_smul (φ : R →+* S) (r : R) (P : LaurentPolynomial R) :
    laurentMap φ (r • P) = φ r • laurentMap φ P := by
  simp only [Algebra.smul_def, map_mul, laurentMap_scalar]

theorem laurentMap_supported (φ : R →+* S) (m : ℕ) {P : LaurentPolynomial R}
    (hP : P ∈ numeratorFiltration R m) : laurentMap φ P ∈ numeratorFiltration S m := by
  classical
  rw [mem_numeratorFiltration]
  intro x hx
  have hx' := Finsupp.mem_support_iff.1 hx
  rw [laurentMap_coefficient] at hx'
  have hPx : P.coeff x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx'
    exact hx' rfl
  exact (mem_numeratorFiltration m P).1 hP x (Finsupp.mem_support_iff.2 hPx)

@[simp] theorem laurentMap_vertex (φ : R →+* S) (j : Fin 6) :
    laurentMap φ (laurentVertex (R := R) j) = laurentVertex (R := S) j := by
  rw [laurentVertex, laurentMap_single, map_one]
  rfl

@[simp] theorem laurentMap_f (φ : R →+* S) (u : R) :
    laurentMap φ (torusPolynomial u) = torusPolynomial (φ u) := by
  simp only [torusPolynomial, map_sub, map_one, map_mul, map_sum,
    laurentMap_scalar, laurentMap_vertex]

/-- The coefficient specialization extends through the actual denominator localization. -/
def actualMap (φ : R →+* S) (u : R) : ActualRing u →+* ActualRing (φ u) :=
  IsLocalization.Away.lift (torusPolynomial u)
    (g := (algebraMap (LaurentPolynomial S) (ActualRing (φ u))).comp (laurentMap φ)) (by
      change IsUnit (algebraMap (LaurentPolynomial S) (ActualRing (φ u))
        (laurentMap φ (torusPolynomial u)))
      rw [laurentMap_f]
      exact IsLocalization.Away.algebraMap_isUnit (torusPolynomial (φ u)))

@[simp] theorem actualMap_algebraMap (φ : R →+* S) (u : R) (P : LaurentPolynomial R) :
    actualMap φ u (algebraMap (LaurentPolynomial R) (ActualRing u) P) =
      algebraMap (LaurentPolynomial S) (ActualRing (φ u)) (laurentMap φ P) := by
  simp only [actualMap, IsLocalization.Away.lift_eq, RingHom.comp_apply]

@[simp] theorem actualMap_scalar (φ : R →+* S) (u r : R) :
    actualMap φ u (algebraMap R (ActualRing u) r) =
      algebraMap S (ActualRing (φ u)) (φ r) := by
  rw [IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (ActualRing u),
    actualMap_algebraMap, laurentMap_scalar,
    ← IsScalarTower.algebraMap_apply S (LaurentPolynomial S) (ActualRing (φ u))]

theorem actualMap_smul (φ : R →+* S) (u r : R) (g : ActualRing u) :
    actualMap φ u (r • g) = φ r • actualMap φ u g := by
  simp only [Algebra.smul_def, map_mul, actualMap_scalar]

@[simp] theorem actualMap_inverseF (φ : R →+* S) (u : R) :
    actualMap φ u (inverseF u) = inverseF (φ u) := by
  have h := congrArg (actualMap φ u) (imageF_mul_inverseF u)
  rw [map_mul, actualMap_algebraMap, laurentMap_f, map_one] at h
  calc
    actualMap φ u (inverseF u) = 1 * actualMap φ u (inverseF u) := (one_mul _).symm
    _ = (inverseF (φ u) * algebraMap (LaurentPolynomial S) (ActualRing (φ u))
        (torusPolynomial (φ u))) * actualMap φ u (inverseF u) := by
      rw [inverseF_mul_imageF]
    _ = inverseF (φ u) * (algebraMap (LaurentPolynomial S) (ActualRing (φ u))
        (torusPolynomial (φ u)) * actualMap φ u (inverseF u)) := mul_assoc _ _ _
    _ = inverseF (φ u) := by rw [h, mul_one]

@[simp] theorem actualMap_factorialPole (φ : R →+* S) (u : R) (n : ℕ) :
    actualMap φ u (factorialPole u n) = factorialPole (φ u) n := by
  simp only [factorialPole, map_mul, map_natCast, map_pow, actualMap_inverseF]

@[simp] theorem actualMap_Gamma (φ : R →+* S) (u : R) (m : ℕ) :
    actualMap φ u (Gamma u m) = Gamma (φ u) m := by
  simp only [Gamma, map_mul, map_natCast, map_pow, actualMap_inverseF]

@[simp] theorem actualMap_actualVertex (φ : R →+* S) (u : R) (j : Fin 6) :
    actualMap φ u (actualVertex u j) = actualVertex (φ u) j := by
  rw [actualVertex, actualMap_algebraMap, laurentMap_vertex]
  rfl

@[simp] theorem actualMap_b (φ : R →+* S) (u : R) (j : Fin 6) :
    actualMap φ u (b u j) = b (φ u) j := by
  simp only [b, map_mul, actualMap_actualVertex, actualMap_inverseF]

@[simp] theorem actualMap_actualMonomial (φ : R →+* S) (u : R) (a : Fin 6 → ℤ) :
    actualMap φ u (actualMonomial u a) = actualMonomial (φ u) a := by
  simp only [actualMonomial, laurentMonomial, actualMap_algebraMap,
    laurentMap_single, map_one]

@[simp] theorem actualMap_numeratorGenerator (φ : R →+* S) (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) :
    actualMap φ u (numeratorGenerator u a n) = numeratorGenerator (φ u) a n := by
  simp only [numeratorGenerator, map_mul, actualMap_actualMonomial, actualMap_factorialPole]

@[simp] theorem actualMap_poleLinearMap (φ : R →+* S) (u : R)
    (m : ℕ) (P : LaurentPolynomial R) :
    actualMap φ u (poleLinearMap u m P) = poleLinearMap (φ u) m (laurentMap φ P) := by
  simp only [poleLinearMap_apply, map_mul, actualMap_algebraMap, map_pow, actualMap_inverseF]

theorem actualMap_preserves_closed (φ : R →+* S) (u : R) {g : ActualRing u}
    (hg : g ∈ FClosed u) : actualMap φ u g ∈ FClosed (φ u) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, n, ha, rfl⟩ := hg
      rw [actualMap_numeratorGenerator]
      exact numeratorGenerator_mem_closed (φ u) a n ha
  | zero => simp
  | add g h _ _ hg hh =>
      rw [map_add]
      exact (FClosed (φ u)).add_mem hg hh
  | smul r g _ hg =>
      rw [actualMap_smul]
      exact (FClosed (φ u)).smul_mem (φ r) hg

theorem actualMap_preserves_interior (φ : R →+* S) (u : R) {g : ActualRing u}
    (hg : g ∈ FInterior u) : actualMap φ u g ∈ FInterior (φ u) := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, n, ha, rfl⟩ := hg
      rw [actualMap_numeratorGenerator]
      exact Submodule.subset_span ⟨a, n, ha, rfl⟩
  | zero => simp
  | add g h _ _ hg hh =>
      rw [map_add]
      exact (FInterior (φ u)).add_mem hg hh
  | smul r g _ hg =>
      rw [actualMap_smul]
      exact (FInterior (φ u)).smul_mem (φ r) hg

def closedMap (φ : R →+* S) (u : R) : FClosed u →ₛₗ[φ] FClosed (φ u) where
  toFun g := ⟨actualMap φ u g, actualMap_preserves_closed φ u g.property⟩
  map_add' g h := Subtype.ext (map_add (actualMap φ u)
    (g : ActualRing u) (h : ActualRing u))
  map_smul' r g := Subtype.ext (actualMap_smul φ u r (g : ActualRing u))

@[simp] theorem closedMap_coe (φ : R →+* S) (u : R) (g : FClosed u) :
    (closedMap φ u g : ActualRing (φ u)) = actualMap φ u g := rfl

theorem actualMap_closed_lift (φ : R →+* S) (hφ : Function.Surjective φ) (u : R)
    {g : ActualRing (φ u)} (hg : g ∈ FClosed (φ u)) :
    ∃ h : ActualRing u, h ∈ FClosed u ∧ actualMap φ u h = g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, n, ha, rfl⟩ := hg
      exact ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha,
        actualMap_numeratorGenerator φ u a n⟩
  | zero => exact ⟨0, (FClosed u).zero_mem, map_zero _⟩
  | add g h _ _ hg hh =>
      obtain ⟨g', hg', he⟩ := hg
      obtain ⟨h', hh', hf⟩ := hh
      exact ⟨g' + h', (FClosed u).add_mem hg' hh', by rw [map_add, he, hf]⟩
  | smul s g _ hg =>
      obtain ⟨r, hr⟩ := hφ s
      obtain ⟨g', hg', he⟩ := hg
      exact ⟨r • g', (FClosed u).smul_mem r hg', by rw [actualMap_smul, hr, he]⟩

theorem closedMap_surjective (φ : R →+* S) (hφ : Function.Surjective φ) (u : R) :
    Function.Surjective (closedMap φ u) := by
  intro g
  obtain ⟨h, hh, he⟩ := actualMap_closed_lift φ hφ u g.property
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

theorem laurentMap_logarithmicDerivation (φ : R →+* S) (w : Exponents →+ ℤ)
    (P : LaurentPolynomial R) :
    laurentMap φ (logarithmicDerivation w P) = logarithmicDerivation w (laurentMap φ P) := by
  induction P using AddMonoidAlgebra.induction_on with
  | of x =>
      simp only [AddMonoidAlgebra.of_apply, logarithmicDerivation_single,
        laurentMap_single, map_mul, map_intCast, map_one]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | smul r P hP => simp only [Derivation.map_smul, laurentMap_smul, hP]

theorem laurentMap_logarithmicPoleNumerator (φ : R →+* S) (u : R) (i : Fin 5)
    (m : ℕ) (P : LaurentPolynomial R) :
    laurentMap φ (logarithmicPoleNumerator u i m P) =
      logarithmicPoleNumerator (φ u) i m (laurentMap φ P) := by
  simp only [logarithmicPoleNumerator, map_add, map_mul,
    laurentMap_logarithmicDerivation, laurentMap_f, laurentMap_smul, map_natCast,
    map_sub, laurentMap_vertex]

theorem actualMap_commutes_actualD_on_closed (φ : R →+* S) (u : R) (i : Fin 5)
    {g : ActualRing u} (hg : g ∈ FClosed u) :
    actualMap φ u (actualD u i g) = actualD (φ u) i (actualMap φ u g) := by
  obtain ⟨m, P, hm, _, hP, rfl⟩ := FClosed_common_pole u hg
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [actualD_poleLinearMap_succ, actualMap_poleLinearMap, actualMap_poleLinearMap,
    actualD_poleLinearMap_succ, laurentMap_logarithmicPoleNumerator]

theorem closedMap_commutes_DClosed (φ : R →+* S) (u : R) (i : Fin 5) (g : FClosed u) :
    closedMap φ u (DClosed u i g) = DClosed (φ u) i (closedMap φ u g) := by
  ext
  exact actualMap_commutes_actualD_on_closed φ u i g.property

theorem closedMap_preserves_exact (φ : R →+* S) (u : R) :
    exactSubmodule u ≤ (exactSubmodule (φ u)).comap (closedMap φ u) := by
  unfold exactSubmodule
  apply iSup_le
  intro i g hg
  obtain ⟨h, rfl⟩ := hg
  change closedMap φ u (DClosed u i h) ∈ exactSubmodule (φ u)
  rw [closedMap_commutes_DClosed]
  exact DClosed_mem_exact (φ u) i (closedMap φ u h)

/-- Specialization of the actual logarithmic residue quotient. -/
def quotientMap (φ : R →+* S) (u : R) :
    ClosedResidueQuotient u →ₛₗ[φ] ClosedResidueQuotient (φ u) :=
  (exactSubmodule u).mapQ (exactSubmodule (φ u)) (closedMap φ u)
    (closedMap_preserves_exact φ u)

@[simp] theorem quotientMap_mkQ (φ : R →+* S) (u : R) (g : FClosed u) :
    quotientMap φ u ((exactSubmodule u).mkQ g) =
      (exactSubmodule (φ u)).mkQ (closedMap φ u g) := rfl

theorem quotientMap_surjective (φ : R →+* S) (hφ : Function.Surjective φ) (u : R) :
    Function.Surjective (quotientMap φ u) := by
  intro g
  obtain ⟨h, rfl⟩ := (exactSubmodule (φ u)).mkQ_surjective g
  obtain ⟨h', rfl⟩ := closedMap_surjective φ hφ u h
  exact ⟨(exactSubmodule u).mkQ h', rfl⟩

end

end WPResidueQuotient.Specialization
