import WPResidueQuotient.Lattice
import WPResidueQuotient.ActualModule
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Localization.Away.Basic

/-!
Actual finite Laurent numerator filtrations and common denominators. The
closed/interior modules here are the literal submodules from ActualModule.
The converse common-pole presentation uses rational factorial inverses;
no such inverse is asserted over an integral coefficient ring.
-/

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators Pointwise

theorem canonicalDegreeNat_add_le (x y : Exponents) :
    canonicalDegreeNat (x + y) ≤ canonicalDegreeNat x + canonicalDegreeNat y := by
  have hn : ∀ i, 0 ≤ (canonicalRepresentative x + canonicalRepresentative y) i := by
    intro i
    exact add_nonneg (canonicalRepresentative_nonneg x i) (canonicalRepresentative_nonneg y i)
  have hd := totalDegree_normalizeExponents_le
    (canonicalRepresentative x + canonicalRepresentative y) hn
  have hq : latticeQ (canonicalRepresentative x + canonicalRepresentative y) = x + y := by
    rw [map_add, latticeQ_canonicalRepresentative, latticeQ_canonicalRepresentative]
  rw [← canonicalRepresentative_latticeQ, hq, totalDegree_add] at hd
  change canonicalDegree (x + y) ≤ canonicalDegree x + canonicalDegree y at hd
  rw [← canonicalDegreeNat_cast (x + y), ← canonicalDegreeNat_cast x,
    ← canonicalDegreeNat_cast y] at hd
  omega

/-- Actual coefficient support, rather than a declared formal generating family. -/
def numeratorFiltration (R : Type*) [CommRing R] (m : ℕ) :
    Submodule R (LaurentPolynomial R) :=
  AddMonoidAlgebra.supported R R {x | canonicalDegreeNat x ≤ m}

theorem mem_numeratorFiltration {R : Type*} [CommRing R] (m : ℕ)
    (P : LaurentPolynomial R) :
    P ∈ numeratorFiltration R m ↔ ∀ x ∈ P.coeff.support, canonicalDegreeNat x ≤ m := by
  rfl

theorem numeratorFiltration_mono {R : Type*} [CommRing R] {m n : ℕ} (h : m ≤ n) :
    numeratorFiltration R m ≤ numeratorFiltration R n :=
  AddMonoidAlgebra.supported_mono (fun _ hx => hx.trans h)

theorem single_mem_numeratorFiltration {R : Type*} [CommRing R] (x : Exponents)
    (r : R) (m : ℕ) (h : canonicalDegreeNat x ≤ m) :
    AddMonoidAlgebra.single x r ∈ numeratorFiltration R m := by
  classical
  rw [mem_numeratorFiltration]
  intro y hy
  have hy' : y ∈ (Finsupp.single x r).support := by
    simpa only [AddMonoidAlgebra.coeff_single] using hy
  have hyx : y = x := Finset.mem_singleton.mp (Finsupp.support_single_subset hy')
  simpa only [hyx] using h

theorem numeratorFiltration_mul {R : Type*} [CommRing R] {m n : ℕ}
    {P Q : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m)
    (hQ : Q ∈ numeratorFiltration R n) : P * Q ∈ numeratorFiltration R (m + n) := by
  classical
  rw [mem_numeratorFiltration] at hP hQ ⊢
  intro z hz
  have hz' := AddMonoidAlgebra.support_coeff_mul_subset P Q hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz'
  exact (canonicalDegreeNat_add_le x y).trans (Nat.add_le_add (hP x hx) (hQ y hy))

theorem one_mem_numeratorFiltration {R : Type*} [CommRing R] (m : ℕ) :
    (1 : LaurentPolynomial R) ∈ numeratorFiltration R m := by
  rw [AddMonoidAlgebra.one_def]
  exact single_mem_numeratorFiltration 0 1 m (by simp)

theorem algebraMap_mem_numeratorFiltration {R : Type*} [CommRing R] (r : R) :
    algebraMap R (LaurentPolynomial R) r ∈ numeratorFiltration R 0 := by
  change AddMonoidAlgebra.single 0 r ∈ numeratorFiltration R 0
  exact single_mem_numeratorFiltration 0 r 0 (by simp)

theorem sixToFive_eq_latticeQ (a : SixExponents) : sixToFive a = latticeQ a := rfl

theorem piSingle_eq_standardExponent (i : Fin 6) :
    (Pi.single i (1 : ℤ) : SixExponents) = standardExponent i := by
  ext j
  simp [standardExponent, Pi.single_apply]

theorem sixVertex_eq_latticeQ_standardExponent (i : Fin 6) :
    sixVertex i = latticeQ (standardExponent i) := by
  rw [sixVertex, sixToFive_eq_latticeQ, piSingle_eq_standardExponent]

theorem sixVertex_degree_le_one (i : Fin 6) : canonicalDegreeNat (sixVertex i) ≤ 1 := by
  rw [sixVertex_eq_latticeQ_standardExponent]
  simpa using canonicalDegreeNat_add_standardExponent_le 0 i

theorem laurentVertex_mem_numeratorFiltration {R : Type*} [CommRing R] (i : Fin 6) :
    laurentVertex (R := R) i ∈ numeratorFiltration R 1 :=
  single_mem_numeratorFiltration (sixVertex i) 1 1 (sixVertex_degree_le_one i)

theorem torusPolynomial_mem_numeratorFiltration {R : Type*} [CommRing R] (u : R) :
    torusPolynomial u ∈ numeratorFiltration R 1 := by
  unfold torusPolynomial
  apply (numeratorFiltration R 1).sub_mem (one_mem_numeratorFiltration 1)
  have hs : (∑ i : Fin 6, laurentVertex (R := R) i) ∈ numeratorFiltration R 1 :=
    (numeratorFiltration R 1).sum_mem (fun i _ => laurentVertex_mem_numeratorFiltration i)
  simpa only [zero_add] using numeratorFiltration_mul
    (algebraMap_mem_numeratorFiltration u) hs

/-- Multiplication by the actual denominator raises the supported degree at most one. -/
theorem numeratorFiltration_mul_f {R : Type*} [CommRing R] (u : R) (m : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) :
    P * torusPolynomial u ∈ numeratorFiltration R (m + 1) :=
  numeratorFiltration_mul hP (torusPolynomial_mem_numeratorFiltration u)

theorem torusPolynomial_pow_mem_numeratorFiltration {R : Type*} [CommRing R]
    (u : R) (k : ℕ) : torusPolynomial u ^ k ∈ numeratorFiltration R k := by
  induction k with
  | zero => simpa using one_mem_numeratorFiltration (R := R) 0
  | succ k ih =>
      rw [pow_succ]
      exact numeratorFiltration_mul_f u k ih

theorem numeratorFiltration_mul_f_pow {R : Type*} [CommRing R] (u : R) (m k : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R m) :
    P * torusPolynomial u ^ k ∈ numeratorFiltration R (m + k) :=
  numeratorFiltration_mul hP (torusPolynomial_pow_mem_numeratorFiltration u k)

/-- Localization of an actual numerator followed by multiplication by a fixed rational element. -/
def numeratorLinearMap {R : Type*} [CommRing R] (u : R) (z : ActualRing u) :
    LaurentPolynomial R →ₗ[R] ActualRing u where
  toFun P := algebraMap (LaurentPolynomial R) (ActualRing u) P * z
  map_add' P Q := by simp [map_add, add_mul]
  map_smul' c P := by
    simp only [Algebra.smul_def, map_mul, mul_assoc]
    change algebraMap (LaurentPolynomial R) (ActualRing u)
        (algebraMap R (LaurentPolynomial R) c) *
        (algebraMap (LaurentPolynomial R) (ActualRing u) P * z) =
      algebraMap R (ActualRing u) c *
        (algebraMap (LaurentPolynomial R) (ActualRing u) P * z)
    rw [← IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (ActualRing u)]

def poleLinearMap {R : Type*} [CommRing R] (u : R) (m : ℕ) :
    LaurentPolynomial R →ₗ[R] ActualRing u := numeratorLinearMap u (inverseF u ^ m)

def factorialNumeratorMap {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    LaurentPolynomial R →ₗ[R] ActualRing u := numeratorLinearMap u (factorialPole u n)

@[simp] theorem poleLinearMap_apply {R : Type*} [CommRing R] (u : R) (m : ℕ)
    (P : LaurentPolynomial R) : poleLinearMap u m P =
    algebraMap (LaurentPolynomial R) (ActualRing u) P * inverseF u ^ m := rfl

@[simp] theorem factorialNumeratorMap_apply {R : Type*} [CommRing R] (u : R) (n : ℕ)
    (P : LaurentPolynomial R) : factorialNumeratorMap u n P =
    algebraMap (LaurentPolynomial R) (ActualRing u) P * factorialPole u n := rfl

/-- Raising a denominator is a proved equality in the actual localization. -/
theorem poleLinearMap_raise {R : Type*} [CommRing R] (u : R)
    (m k : ℕ) (P : LaurentPolynomial R) :
    poleLinearMap u (m + k) (P * torusPolynomial u ^ k) = poleLinearMap u m P := by
  simp only [poleLinearMap_apply, map_mul, map_pow]
  have hc : algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ k *
      inverseF u ^ k = 1 := by
    rw [← mul_pow, imageF_mul_inverseF, one_pow]
  rw [pow_add]
  calc
    _ = algebraMap (LaurentPolynomial R) (ActualRing u) P *
        (algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ k *
          inverseF u ^ k) * inverseF u ^ m := by ring
    _ = _ := by rw [hc, mul_one]

def canonicalAsNat (x : Exponents) : Fin 6 → ℕ :=
  fun i => (canonicalRepresentative x i).toNat

theorem canonicalAsNat_cast (x : Exponents) :
    (fun i => (canonicalAsNat x i : ℤ)) = canonicalRepresentative x := by
  ext i
  exact Int.toNat_of_nonneg (canonicalRepresentative_nonneg x i)

theorem canonicalAsNat_sum (x : Exponents) :
    (∑ i, canonicalAsNat x i) = canonicalDegreeNat x :=
  (canonicalDegreeNat_eq_sum_toNat x).symm

theorem latticeQ_nonnegative_degree_le (a : Fin 6 → ℕ) :
    canonicalDegreeNat (latticeQ (fun i => (a i : ℤ))) ≤ ∑ i, a i := by
  have h := totalDegree_normalizeExponents_le (fun i => (a i : ℤ))
    (fun i => Int.natCast_nonneg (a i))
  rw [← canonicalRepresentative_latticeQ] at h
  change canonicalDegree (latticeQ (fun i => (a i : ℤ))) ≤ ∑ i, (a i : ℤ) at h
  rw [← canonicalDegreeNat_cast] at h
  rw [← Nat.cast_sum] at h
  omega

def canonicalNumeratorGenerator {R : Type*} [CommRing R] (u : R)
    (x : Exponents) (n : ℕ) : ActualRing u :=
  factorialNumeratorMap u n (AddMonoidAlgebra.single x 1)

theorem numeratorGenerator_eq_canonical {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) :
    numeratorGenerator u a n =
      canonicalNumeratorGenerator u (latticeQ (fun i => (a i : ℤ))) n := rfl

theorem canonicalNumeratorGenerator_as_nonnegative {R : Type*} [CommRing R]
    (u : R) (x : Exponents) (n : ℕ) :
    canonicalNumeratorGenerator u x n = numeratorGenerator u (canonicalAsNat x) n := by
  rw [numeratorGenerator_eq_canonical, canonicalAsNat_cast, latticeQ_canonicalRepresentative]

def canonicalClosedGenerators {R : Type*} [CommRing R] (u : R) : Set (ActualRing u) :=
  {g | ∃ x n, canonicalDegreeNat x ≤ n + 1 ∧ g = canonicalNumeratorGenerator u x n}

def canonicalInteriorGenerators {R : Type*} [CommRing R] (u : R) : Set (ActualRing u) :=
  {g | ∃ x n, canonicalDegreeNat x ≤ n ∧ g = canonicalNumeratorGenerator u x n}

theorem closedGenerators_eq_canonical {R : Type*} [CommRing R] (u : R) :
    closedGenerators u = canonicalClosedGenerators u := by
  ext g
  constructor
  · rintro ⟨a, n, ha, rfl⟩
    exact ⟨latticeQ (fun i => (a i : ℤ)), n,
      (latticeQ_nonnegative_degree_le a).trans ha, numeratorGenerator_eq_canonical u a n⟩
  · rintro ⟨x, n, hx, rfl⟩
    refine ⟨canonicalAsNat x, n, ?_, canonicalNumeratorGenerator_as_nonnegative u x n⟩
    rw [canonicalAsNat_sum]
    exact hx

theorem interiorGenerators_eq_canonical {R : Type*} [CommRing R] (u : R) :
    interiorGenerators u = canonicalInteriorGenerators u := by
  ext g
  constructor
  · rintro ⟨a, n, ha, rfl⟩
    exact ⟨latticeQ (fun i => (a i : ℤ)), n,
      (latticeQ_nonnegative_degree_le a).trans ha, numeratorGenerator_eq_canonical u a n⟩
  · rintro ⟨x, n, hx, rfl⟩
    refine ⟨canonicalAsNat x, n, ?_, canonicalNumeratorGenerator_as_nonnegative u x n⟩
    rw [canonicalAsNat_sum]
    exact hx

theorem FClosed_eq_canonical_span {R : Type*} [CommRing R] (u : R) :
    FClosed u = Submodule.span R (canonicalClosedGenerators u) := by
  rw [FClosed, closedGenerators_eq_canonical]

theorem FInterior_eq_canonical_span {R : Type*} [CommRing R] (u : R) :
    FInterior u = Submodule.span R (canonicalInteriorGenerators u) := by
  rw [FInterior, interiorGenerators_eq_canonical]

theorem factorialNumeratorMap_mem_closed {R : Type*} [CommRing R] (u : R) (n : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R (n + 1)) :
    factorialNumeratorMap u n P ∈ FClosed u := by
  rw [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single] at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨x, hx, rfl⟩ := hP
      rw [FClosed_eq_canonical_span]
      exact Submodule.subset_span ⟨x, n, hx, rfl⟩
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact (FClosed u).add_mem hP hQ
  | smul c P _ hP =>
      rw [map_smul]
      exact (FClosed u).smul_mem c hP

theorem factorialNumeratorMap_mem_interior {R : Type*} [CommRing R] (u : R) (n : ℕ)
    {P : LaurentPolynomial R} (hP : P ∈ numeratorFiltration R n) :
    factorialNumeratorMap u n P ∈ FInterior u := by
  rw [numeratorFiltration, AddMonoidAlgebra.supported_eq_span_single] at hP
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨x, hx, rfl⟩ := hP
      rw [FInterior_eq_canonical_span]
      exact Submodule.subset_span ⟨x, n, hx, rfl⟩
  | zero => simp
  | add P Q _ _ hP hQ =>
      rw [map_add]
      exact (FInterior u).add_mem hP hQ
  | smul c P _ hP =>
      rw [map_smul]
      exact (FInterior u).smul_mem c hP

/-- Exact support-filtration image presentation of the literal closed module. -/
theorem FClosed_eq_iSup_supported_images {R : Type*} [CommRing R] (u : R) :
    FClosed u = ⨆ n : ℕ, (numeratorFiltration R (n + 1)).map (factorialNumeratorMap u n) := by
  apply le_antisymm
  · rw [FClosed_eq_canonical_span]
    apply Submodule.span_le.2
    rintro g ⟨x, n, hx, rfl⟩
    exact (le_iSup (fun k : ℕ => (numeratorFiltration R (k + 1)).map
      (factorialNumeratorMap u k)) n) ⟨AddMonoidAlgebra.single x 1,
        single_mem_numeratorFiltration x 1 (n + 1) hx, rfl⟩
  · apply iSup_le
    intro n g hg
    obtain ⟨P, hP, rfl⟩ := hg
    exact factorialNumeratorMap_mem_closed u n hP

/-- Exact support-filtration image presentation of the literal interior module. -/
theorem FInterior_eq_iSup_supported_images {R : Type*} [CommRing R] (u : R) :
    FInterior u = ⨆ n : ℕ, (numeratorFiltration R n).map (factorialNumeratorMap u n) := by
  apply le_antisymm
  · rw [FInterior_eq_canonical_span]
    apply Submodule.span_le.2
    rintro g ⟨x, n, hx, rfl⟩
    exact (le_iSup (fun k : ℕ => (numeratorFiltration R k).map
      (factorialNumeratorMap u k)) n) ⟨AddMonoidAlgebra.single x 1,
        single_mem_numeratorFiltration x 1 n hx, rfl⟩
  · apply iSup_le
    intro n g hg
    obtain ⟨P, hP, rfl⟩ := hg
    exact factorialNumeratorMap_mem_interior u n hP

/-- A literal supported common numerator at a positive pole; `δ=0,1` give closed/interior bounds. -/
def HasCommonPole {R : Type*} [CommRing R] (u : R) (δ : ℕ) (g : ActualRing u) : Prop :=
  ∃ (m : ℕ) (P : LaurentPolynomial R), 0 < m ∧ δ ≤ m ∧
    P ∈ numeratorFiltration R (m - δ) ∧ g = poleLinearMap u m P

theorem hasCommonPole_zero {R : Type*} [CommRing R] (u : R) (δ : ℕ) :
    HasCommonPole u δ 0 := by
  refine ⟨δ + 1, 0, by omega, by omega, (numeratorFiltration R _).zero_mem, ?_⟩
  exact (map_zero (poleLinearMap u (δ + 1))).symm

theorem hasCommonPole_add {R : Type*} [CommRing R] (u : R) (δ : ℕ)
    {g h : ActualRing u} (hg : HasCommonPole u δ g) (hh : HasCommonPole u δ h) :
    HasCommonPole u δ (g + h) := by
  obtain ⟨m, P, hm, hδm, hP, rfl⟩ := hg
  obtain ⟨n, Q, hn, hδn, hQ, rfl⟩ := hh
  refine ⟨m + n, P * torusPolynomial u ^ n + Q * torusPolynomial u ^ m,
    by omega, by omega, ?_, ?_⟩
  · apply (numeratorFiltration R (m + n - δ)).add_mem
    · have h := numeratorFiltration_mul_f_pow u (m - δ) n hP
      have he : m - δ + n = m + n - δ := by omega
      simpa only [he] using h
    · have h := numeratorFiltration_mul_f_pow u (n - δ) m hQ
      have he : n - δ + m = m + n - δ := by omega
      simpa only [he] using h
  · rw [map_add, poleLinearMap_raise]
    have he : m + n = n + m := Nat.add_comm m n
    rw [he, poleLinearMap_raise]

theorem hasCommonPole_smul {R : Type*} [CommRing R] (u : R) (δ : ℕ)
    (c : R) {g : ActualRing u} (hg : HasCommonPole u δ g) :
    HasCommonPole u δ (c • g) := by
  obtain ⟨m, P, hm, hδm, hP, rfl⟩ := hg
  exact ⟨m, c • P, hm, hδm, (numeratorFiltration R _).smul_mem c hP,
    (map_smul (poleLinearMap u m) c P).symm⟩

def commonPoleModule {R : Type*} [CommRing R] (u : R) (δ : ℕ) :
    Submodule R (ActualRing u) where
  carrier := {g | HasCommonPole u δ g}
  zero_mem' := hasCommonPole_zero u δ
  add_mem' := hasCommonPole_add u δ
  smul_mem' c _ h := hasCommonPole_smul u δ c h

theorem factorialNumeratorMap_as_pole {R : Type*} [CommRing R] (u : R) (n : ℕ)
    (P : LaurentPolynomial R) : factorialNumeratorMap u n P =
      poleLinearMap u (n + 1) ((n.factorial : R) • P) := by
  simp only [factorialNumeratorMap_apply, poleLinearMap_apply, factorialPole,
    Algebra.smul_def, map_mul, map_natCast]
  ring

theorem FClosed_le_commonPoleModule {R : Type*} [CommRing R] (u : R) :
    FClosed u ≤ commonPoleModule u 0 := by
  rw [FClosed_eq_canonical_span]
  apply Submodule.span_le.2
  rintro g ⟨x, n, hx, rfl⟩
  refine ⟨n + 1, (n.factorial : R) • AddMonoidAlgebra.single x 1,
    by omega, by omega, ?_, ?_⟩
  · exact (numeratorFiltration R (n + 1)).smul_mem _
      (single_mem_numeratorFiltration x 1 (n + 1) hx)
  · exact factorialNumeratorMap_as_pole u n _

theorem FInterior_le_commonPoleModule {R : Type*} [CommRing R] (u : R) :
    FInterior u ≤ commonPoleModule u 1 := by
  rw [FInterior_eq_canonical_span]
  apply Submodule.span_le.2
  rintro g ⟨x, n, hx, rfl⟩
  refine ⟨n + 1, (n.factorial : R) • AddMonoidAlgebra.single x 1,
    by omega, by omega, ?_, ?_⟩
  · simpa only [Nat.add_sub_cancel] using (numeratorFiltration R n).smul_mem
      (n.factorial : R) (single_mem_numeratorFiltration x 1 n hx)
  · exact factorialNumeratorMap_as_pole u n _

theorem FClosed_common_pole {R : Type*} [CommRing R] (u : R)
    {g : ActualRing u} (hg : g ∈ FClosed u) : HasCommonPole u 0 g :=
  FClosed_le_commonPoleModule u hg

theorem FInterior_common_pole {R : Type*} [CommRing R] (u : R)
    {g : ActualRing u} (hg : g ∈ FInterior u) : HasCommonPole u 1 g :=
  FInterior_le_commonPoleModule u hg

theorem finite_sum_common_pole {R : Type*} [CommRing R] (u : R) (δ : ℕ)
    {ι : Type*} (s : Finset ι) (g : ι → ActualRing u)
    (h : ∀ i ∈ s, HasCommonPole u δ (g i)) :
    HasCommonPole u δ (∑ i ∈ s, g i) := (commonPoleModule u δ).sum_mem h

/-- Only the rational coefficient algebra is used for inverse factorials. -/
def rationalFactorialInverse {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ) : R :=
  algebraMap ℚ R ((n.factorial : ℚ)⁻¹)

theorem rationalFactorialInverse_mul {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ) :
    rationalFactorialInverse (R := R) n * (n.factorial : R) = 1 := by
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have h := congrArg (algebraMap ℚ R) (inv_mul_cancel₀ hn)
  simpa only [rationalFactorialInverse, map_mul, map_natCast, map_one] using h

theorem rationalFactorialInverse_isUnit {R : Type*} [CommRing R] [Algebra ℚ R] (n : ℕ) :
    IsUnit (n.factorial : R) := by
  exact IsUnit.of_mul_eq_one_right _ (rationalFactorialInverse_mul (R := R) n)

theorem pole_as_factorialNumeratorMap {R : Type*} [CommRing R] [Algebra ℚ R]
    (u : R) (n : ℕ) (P : LaurentPolynomial R) :
    poleLinearMap u (n + 1) P = factorialNumeratorMap u n
      (rationalFactorialInverse (R := R) n • P) := by
  rw [factorialNumeratorMap_as_pole, smul_smul]
  have hi : (n.factorial : R) * rationalFactorialInverse (R := R) n = 1 := by
    rw [mul_comm]
    exact rationalFactorialInverse_mul n
  rw [hi, one_smul]

theorem commonPoleModule_le_FClosed {R : Type*} [CommRing R] [Algebra ℚ R] (u : R) :
    commonPoleModule u 0 ≤ FClosed u := by
  rintro g ⟨m, P, hm, _, hP, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [pole_as_factorialNumeratorMap]
  exact factorialNumeratorMap_mem_closed u n
    ((numeratorFiltration R (n + 1)).smul_mem _ hP)

theorem commonPoleModule_le_FInterior {R : Type*} [CommRing R] [Algebra ℚ R] (u : R) :
    commonPoleModule u 1 ≤ FInterior u := by
  rintro g ⟨m, P, hm, _, hP, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [pole_as_factorialNumeratorMap]
  apply factorialNumeratorMap_mem_interior u n
  simpa only [Nat.add_sub_cancel] using (numeratorFiltration R _).smul_mem
    (rationalFactorialInverse (R := R) n) hP

theorem FClosed_eq_commonPoleModule {R : Type*} [CommRing R] [Algebra ℚ R] (u : R) :
    FClosed u = commonPoleModule u 0 :=
  le_antisymm (FClosed_le_commonPoleModule u) (commonPoleModule_le_FClosed u)

theorem FInterior_eq_commonPoleModule {R : Type*} [CommRing R] [Algebra ℚ R] (u : R) :
    FInterior u = commonPoleModule u 1 :=
  le_antisymm (FInterior_le_commonPoleModule u) (commonPoleModule_le_FInterior u)

theorem actualLaurent_algebraMap_injective {R : Type*} [CommRing R] [IsDomain R] (u : R) :
    Function.Injective (algebraMap (LaurentPolynomial R) (ActualRing u)) :=
  IsLocalization.injective (ActualRing u)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (torusPolynomial_ne_zero u))

theorem poleLinearMap_clear_denominator {R : Type*} [CommRing R] (u : R)
    (m : ℕ) (P : LaurentPolynomial R) :
    poleLinearMap u m P *
      algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ m =
      algebraMap (LaurentPolynomial R) (ActualRing u) P := by
  rw [poleLinearMap_apply]
  have h : inverseF u ^ m *
      algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ m = 1 := by
    rw [← mul_pow, inverseF_mul_imageF, one_pow]
  rw [mul_assoc, h, mul_one]

theorem poleLinearMap_injective {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (m : ℕ) : Function.Injective (poleLinearMap u m) := by
  intro P Q h
  apply actualLaurent_algebraMap_injective u
  have hc := congrArg (fun z : ActualRing u => z *
    algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ m) h
  simpa only [poleLinearMap_clear_denominator] using hc

/-- A zero actual fraction has zero numerator over the domain coefficient ring. -/
theorem poleLinearMap_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (m : ℕ) (P : LaurentPolynomial R) : poleLinearMap u m P = 0 ↔ P = 0 := by
  constructor
  · intro h
    apply poleLinearMap_injective u m
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- All equality relations are literal common-denominator numerator equalities. -/
theorem poleLinearMap_eq_iff_cross_multiply {R : Type*} [CommRing R] [IsDomain R]
    (u : R) (m n : ℕ) (P Q : LaurentPolynomial R) :
    poleLinearMap u m P = poleLinearMap u n Q ↔
      P * torusPolynomial u ^ n = Q * torusPolynomial u ^ m := by
  have hP := poleLinearMap_raise u m n P
  have hQ := poleLinearMap_raise u n m Q
  rw [Nat.add_comm n m] at hQ
  constructor
  · intro h
    apply poleLinearMap_injective u (m + n)
    rw [hP, hQ, h]
  · intro h
    rw [← hP, ← hQ, h]

end

end WPResidueQuotient
