import WPResidueQuotient.LaurentDerivation
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

def sixToFive (a : Fin 6 → ℤ) : Exponents := fun i => a i.castSucc - a 5

def sixVertex (i : Fin 6) : Exponents := sixToFive (Pi.single i 1)

theorem sixVertex_ne_zero (i : Fin 6) : sixVertex i ≠ 0 := by
  fin_cases i <;> decide

def laurentMonomial {R : Type*} [CommRing R] (a : Fin 6 → ℤ) :
    LaurentPolynomial R := AddMonoidAlgebra.single (sixToFive a) 1

def laurentVertex {R : Type*} [CommRing R] (i : Fin 6) : LaurentPolynomial R :=
  AddMonoidAlgebra.single (sixVertex i) 1

def torusPolynomial {R : Type*} [CommRing R] (u : R) : LaurentPolynomial R :=
  1 - algebraMap R (LaurentPolynomial R) u * ∑ i : Fin 6, laurentVertex i

theorem torusPolynomial_coefficient_zero {R : Type*} [CommRing R] (u : R) :
    (torusPolynomial u).coeff 0 = 1 := by
  simp [torusPolynomial, laurentVertex, AddMonoidAlgebra.coeff_mul,
    sixVertex_ne_zero, Ne.symm]

theorem torusPolynomial_ne_zero {R : Type*} [CommRing R] [Nontrivial R] (u : R) :
    torusPolynomial u ≠ 0 := by
  intro h
  have := congrArg (fun P : LaurentPolynomial R => P.coeff 0) h
  simp [torusPolynomial_coefficient_zero] at this

abbrev ActualRing {R : Type*} [CommRing R] (u : R) :=
  Localization.Away (torusPolynomial u)

instance actualRing_isDomain {R : Type*} [CommRing R] [IsDomain R] (u : R) :
    IsDomain (ActualRing u) := Localization.Away.isDomain (torusPolynomial_ne_zero u)

theorem actual_algebraMap_injective {R : Type*} [CommRing R] [IsDomain R] (u : R) :
    Function.Injective (algebraMap (LaurentPolynomial R) (ActualRing u)) :=
  IsLocalization.injective (ActualRing u)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (torusPolynomial_ne_zero u))

def actualMonomial {R : Type*} [CommRing R] (u : R) (a : Fin 6 → ℤ) : ActualRing u :=
  algebraMap (LaurentPolynomial R) (ActualRing u) (laurentMonomial a)

def actualVertex {R : Type*} [CommRing R] (u : R) (i : Fin 6) : ActualRing u :=
  algebraMap (LaurentPolynomial R) (ActualRing u) (laurentVertex i)

def inverseF {R : Type*} [CommRing R] (u : R) : ActualRing u :=
  IsLocalization.Away.invSelf (torusPolynomial u)

/-- Pole `n+1`, with exactly the factorial numerator of the frozen proof. -/
def factorialPole {R : Type*} [CommRing R] (u : R) (n : ℕ) : ActualRing u :=
  (n.factorial : ActualRing u) * inverseF u ^ (n + 1)

def Gamma {R : Type*} [CommRing R] (u : R) (m : ℕ) : ActualRing u :=
  ((m - 1).factorial : ActualRing u) * inverseF u ^ m

@[simp] theorem Gamma_succ {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    Gamma u (n + 1) = factorialPole u n := by
  simp [Gamma, factorialPole]

def b {R : Type*} [CommRing R] (u : R) (i : Fin 6) : ActualRing u :=
  actualVertex u i * inverseF u

def numeratorGenerator {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) : ActualRing u :=
  actualMonomial u (fun i => (a i : ℤ)) * factorialPole u n

/-- Equivalent nonnegative presentations are used before canonicalization. -/
def closedGenerators {R : Type*} [CommRing R] (u : R) : Set (ActualRing u) :=
  {g | ∃ (a : Fin 6 → ℕ) (n : ℕ), (∑ i, a i) ≤ n + 1 ∧
    g = numeratorGenerator u a n}

def interiorGenerators {R : Type*} [CommRing R] (u : R) : Set (ActualRing u) :=
  {g | ∃ (a : Fin 6 → ℕ) (n : ℕ), (∑ i, a i) ≤ n ∧
    g = numeratorGenerator u a n}

def FClosed {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  Submodule.span R (closedGenerators u)

def FInterior {R : Type*} [CommRing R] (u : R) : Submodule R (ActualRing u) :=
  Submodule.span R (interiorGenerators u)

theorem FInterior_le_FClosed {R : Type*} [CommRing R] (u : R) :
    FInterior u ≤ FClosed u := by
  apply Submodule.span_mono
  rintro g ⟨a, n, h, rfl⟩
  exact ⟨a, n, h.trans (Nat.le_succ n), rfl⟩

theorem factorialPole_mem_interior {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    factorialPole u n ∈ FInterior u := by
  apply Submodule.subset_span
  refine ⟨fun _ => 0, n, by simp, ?_⟩
  change factorialPole u n =
    algebraMap (LaurentPolynomial R) (ActualRing u) (AddMonoidAlgebra.single 0 1) *
      factorialPole u n
  simp [← AddMonoidAlgebra.one_def]

def actualD {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    Derivation R (ActualRing u) (ActualRing u) :=
  localizedLogarithmic (torusPolynomial u) i

theorem actualScalar {R : Type*} [CommRing R] (u r : R) :
    algebraMap (LaurentPolynomial R) (ActualRing u) (AddMonoidAlgebra.single 0 r) =
      algebraMap R (ActualRing u) r :=
  (IsScalarTower.algebraMap_apply R (LaurentPolynomial R) (ActualRing u) r).symm

theorem logarithmicDerivation_vertex {R : Type*} [CommRing R]
    (i : Fin 5) (j : Fin 6) :
    logarithmicDerivation (coordinateWeight i) (laurentVertex (R := R) j) =
      (if j = i.castSucc then laurentVertex j else 0) -
        (if j = 5 then laurentVertex j else 0) := by
  classical
  have hw : coordinateWeight i (sixVertex j) =
      (if j = i.castSucc then (1 : ℤ) else 0) - (if j = 5 then 1 else 0) := by
    simp only [coordinateWeight_apply, sixVertex, sixToFive, Pi.single_apply]
    simp only [eq_comm]
  simp only [laurentVertex, logarithmicDerivation_single, hw, mul_one]
  have hlast : i.castSucc ≠ (5 : Fin 6) := Fin.castSucc_ne_last i
  by_cases hi : j = i.castSucc <;> by_cases hj : j = 5 <;>
    simp [hi, hj, hlast, Ne.symm hlast]

theorem logarithmicDerivation_vertex_sum {R : Type*} [CommRing R] (i : Fin 5) :
    logarithmicDerivation (coordinateWeight i) (∑ j : Fin 6, laurentVertex (R := R) j) =
      laurentVertex i.castSucc - laurentVertex 5 := by
  simp only [map_sum, logarithmicDerivation_vertex, Finset.sum_sub_distrib]
  simp

theorem logarithmicDerivation_f {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    logarithmicDerivation (coordinateWeight i) (torusPolynomial u) =
      -algebraMap R (LaurentPolynomial R) u *
        (laurentVertex i.castSucc - laurentVertex 5) := by
  rw [torusPolynomial, Derivation.map_sub, Derivation.leibniz,
    logarithmicDerivation_vertex_sum]
  simp [smul_eq_mul]

theorem actualD_f {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    actualD u i (algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u)) =
      -algebraMap R (ActualRing u) u *
        (actualVertex u i.castSucc - actualVertex u 5) := by
  simp [actualD, localizedLogarithmic, logarithmicDerivation_f, actualVertex,
    actualScalar]

theorem actualD_inverseF {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    actualD u i (inverseF u) = algebraMap R (ActualRing u) u *
      (actualVertex u i.castSucc - actualVertex u 5) * inverseF u ^ 2 := by
  rw [inverseF, derivation_invSelf, actualD_f]
  ring

theorem actualD_factorialPole {R : Type*} [CommRing R] (u : R)
    (i : Fin 5) (n : ℕ) :
    actualD u i (factorialPole u n) = algebraMap R (ActualRing u) u *
      (actualVertex u i.castSucc - actualVertex u 5) * factorialPole u (n + 1) := by
  simp only [factorialPole, Derivation.leibniz, Derivation.map_natCast, smul_zero,
    add_zero, Derivation.leibniz_pow, Nat.add_sub_cancel]
  rw [actualD_inverseF, Nat.factorial_succ]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ]
  ring

theorem sixToFive_add (a c : Fin 6 → ℤ) :
    sixToFive (a + c) = sixToFive a + sixToFive c := by
  ext i
  simp [sixToFive]
  ring

theorem actualMonomial_add {R : Type*} [CommRing R] (u : R)
    (a c : Fin 6 → ℤ) :
    actualMonomial u (a + c) = actualMonomial u a * actualMonomial u c := by
  simp [actualMonomial, laurentMonomial, sixToFive_add,
    AddMonoidAlgebra.single_mul_single, ← map_mul]

def addNumeratorExponent (a : Fin 6 → ℕ) (j : Fin 6) : Fin 6 → ℕ :=
  a + Pi.single j 1

theorem addNumeratorExponent_sum (a : Fin 6 → ℕ) (j : Fin 6) :
    (∑ k, addNumeratorExponent a j k) = (∑ k, a k) + 1 := by
  classical
  simp [addNumeratorExponent, Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply]

theorem addNumeratorExponent_cast (a : Fin 6 → ℕ) (j : Fin 6) :
    (fun k => (addNumeratorExponent a j k : ℤ)) =
      (fun k => (a k : ℤ)) + Pi.single j 1 := by
  classical
  ext k
  simp [addNumeratorExponent, Pi.single_apply]

theorem numeratorGenerator_add {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (j : Fin 6) (n : ℕ) :
    numeratorGenerator u (addNumeratorExponent a j) n =
      actualMonomial u (fun k => (a k : ℤ)) * actualVertex u j * factorialPole u n := by
  rw [numeratorGenerator, addNumeratorExponent_cast, actualMonomial_add]
  rfl

theorem actualD_monomial {R : Type*} [CommRing R] (u : R)
    (i : Fin 5) (a : Fin 6 → ℤ) :
    actualD u i (actualMonomial u a) =
      algebraMap R (ActualRing u) ((a i.castSucc - a 5 : ℤ) : R) * actualMonomial u a := by
  exact localizedLogarithmic_monomial (torusPolynomial u) i (sixToFive a)

theorem actualD_numeratorGenerator {R : Type*} [CommRing R] (u : R)
    (i : Fin 5) (a : Fin 6 → ℕ) (n : ℕ) :
    actualD u i (numeratorGenerator u a n) =
      algebraMap R (ActualRing u) ((a i.castSucc : R) - (a 5 : R)) *
        numeratorGenerator u a n + algebraMap R (ActualRing u) u *
        (numeratorGenerator u (addNumeratorExponent a i.castSucc) (n + 1) -
          numeratorGenerator u (addNumeratorExponent a 5) (n + 1)) := by
  rw [numeratorGenerator, Derivation.leibniz, actualD_monomial, actualD_factorialPole]
  rw [numeratorGenerator_add, numeratorGenerator_add]
  simp only [smul_eq_mul, Int.cast_sub, Int.cast_natCast]
  ring

theorem numeratorGenerator_mem_closed {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) (h : (∑ i, a i) ≤ n + 1) :
    numeratorGenerator u a n ∈ FClosed u :=
  Submodule.subset_span ⟨a, n, h, rfl⟩

theorem actualD_preserves_closed {R : Type*} [CommRing R] (u : R) (i : Fin 5)
    {g : ActualRing u} (hg : g ∈ FClosed u) : actualD u i g ∈ FClosed u := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨a, n, ha, rfl⟩ := hg
      rw [actualD_numeratorGenerator]
      apply (FClosed u).add_mem
      · simpa only [Algebra.smul_def] using (FClosed u).smul_mem
          ((a i.castSucc : R) - (a 5 : R)) (numeratorGenerator_mem_closed u a n ha)
      · rw [← Algebra.smul_def]
        apply (FClosed u).smul_mem
        apply (FClosed u).sub_mem
        · apply numeratorGenerator_mem_closed
          rw [addNumeratorExponent_sum]
          omega
        · apply numeratorGenerator_mem_closed
          rw [addNumeratorExponent_sum]
          omega
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (FClosed u).add_mem ihx ihy
  | smul r x hx ih =>
      rw [Derivation.map_smul]
      exact (FClosed u).smul_mem r ih

def DClosed {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    FClosed u →ₗ[R] FClosed u :=
  (((actualD u i).toLinearMap).comp (FClosed u).subtype).codRestrict (FClosed u)
    (fun g => actualD_preserves_closed u i g.property)

/-- The actual sum of logarithmic derivative images. -/
def exactSubmodule {R : Type*} [CommRing R] (u : R) : Submodule R (FClosed u) :=
  iSup (fun i : Fin 5 => LinearMap.range (DClosed u i))

abbrev ClosedResidueQuotient {R : Type*} [CommRing R] (u : R) :=
  (FClosed u) ⧸ exactSubmodule u

theorem DClosed_mem_exact {R : Type*} [CommRing R] (u : R) (i : Fin 5)
    (g : FClosed u) : DClosed u i g ∈ exactSubmodule u :=
  (le_iSup (fun i : Fin 5 => LinearMap.range (DClosed u i)) i)
    (LinearMap.mem_range_self (DClosed u i) g)

def exactAggregate {R : Type*} [CommRing R] (u : R) :
    (Fin 5 → FClosed u) →ₗ[R] FClosed u :=
  ∑ i : Fin 5, (DClosed u i).comp (LinearMap.proj i)

@[simp] theorem exactAggregate_apply {R : Type*} [CommRing R] (u : R)
    (g : Fin 5 → FClosed u) :
    exactAggregate u g = ∑ i : Fin 5, DClosed u i (g i) := by simp [exactAggregate]

theorem exactAggregate_range {R : Type*} [CommRing R] (u : R) :
    LinearMap.range (exactAggregate u) = exactSubmodule u := by
  classical
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    rw [exactAggregate_apply]
    exact (exactSubmodule u).sum_mem (fun i _ => DClosed_mem_exact u i (g i))
  · apply iSup_le
    intro i
    rintro x ⟨g, rfl⟩
    refine ⟨Pi.single i g, ?_⟩
    simp [exactAggregate_apply, Pi.single_apply, apply_ite]

theorem imageF {R : Type*} [CommRing R] (u : R) :
    algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) =
      1 - algebraMap R (ActualRing u) u * ∑ i : Fin 6, actualVertex u i := by
  simp [torusPolynomial, actualVertex, map_sum, actualScalar]

theorem imageF_mul_inverseF {R : Type*} [CommRing R] (u : R) :
    algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) * inverseF u = 1 :=
  IsLocalization.Away.mul_invSelf (torusPolynomial u)

theorem inverseF_mul_imageF {R : Type*} [CommRing R] (u : R) :
    inverseF u * algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) = 1 := by
  rw [mul_comm]
  exact imageF_mul_inverseF u

theorem inverseF_power_cancel {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    inverseF u ^ (n + 1) *
      algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) = inverseF u ^ n := by
  rw [pow_succ, mul_assoc, inverseF_mul_imageF, mul_one]

theorem factorialPole_raise {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    (n + 1 : ActualRing u) * factorialPole u n =
      factorialPole u (n + 1) *
        algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) := by
  simp only [factorialPole, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_assoc, inverseF_power_cancel]
  ring

theorem factorialPole_pole_relation {R : Type*} [CommRing R] (u : R) (n : ℕ) :
    (n + 1 : ActualRing u) * factorialPole u n =
      factorialPole u (n + 1) - algebraMap R (ActualRing u) u *
        ∑ i : Fin 6, actualVertex u i * factorialPole u (n + 1) := by
  rw [factorialPole_raise, imageF, ← Finset.sum_mul]
  ring

theorem factorialPole_common_pole {R : Type*} [CommRing R] (u : R)
    (n M : ℕ) (h : n + 1 ≤ M) :
    factorialPole u n = (n.factorial : ActualRing u) *
      algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ (M - (n + 1)) *
        inverseF u ^ M := by
  have hp : M = (M - (n + 1)) + (n + 1) := (Nat.sub_add_cancel h).symm
  rw [hp, pow_add]
  have hpow := congrArg (fun x : ActualRing u => x ^ (M - (n + 1)))
    (imageF_mul_inverseF u)
  rw [mul_pow, one_pow] at hpow
  change (n.factorial : ActualRing u) * inverseF u ^ (n + 1) = _
  have he : M - (n + 1) + (n + 1) - (n + 1) = M - (n + 1) := by omega
  rw [he]
  calc
    _ = (n.factorial : ActualRing u) *
        (algebraMap (LaurentPolynomial R) (ActualRing u) (torusPolynomial u) ^ (M - (n + 1)) *
          inverseF u ^ (M - (n + 1))) * inverseF u ^ (n + 1) := by rw [hpow, mul_one]
    _ = _ := by ring

end

end WPResidueQuotient
