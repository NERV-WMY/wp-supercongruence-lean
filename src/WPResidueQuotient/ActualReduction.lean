import WPResidueQuotient.ActualModule
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

namespace WPResidueQuotient

noncomputable section

open scoped BigOperators

def DSix {R : Type*} [CommRing R] (u : R) (i : Fin 6) :
    Derivation R (ActualRing u) (ActualRing u) := Fin.lastCases 0 (actualD u) i

@[simp] theorem DSix_castSucc {R : Type*} [CommRing R] (u : R) (i : Fin 5) :
    DSix u i.castSucc = actualD u i := by simp [DSix]

@[simp] theorem DSix_last {R : Type*} [CommRing R] (u : R) :
    DSix u (Fin.last 5) = 0 := Fin.lastCases_last

def Dik {R : Type*} [CommRing R] (u : R) (i k : Fin 6) :
    Derivation R (ActualRing u) (ActualRing u) := DSix u i - DSix u k

theorem DSix_numeratorGenerator {R : Type*} [CommRing R] (u : R)
    (i : Fin 6) (a : Fin 6 → ℕ) (n : ℕ) :
    DSix u i (numeratorGenerator u a n) =
      ((a i : ActualRing u) - (a 5 : ActualRing u)) * numeratorGenerator u a n +
        algebraMap R (ActualRing u) u *
        (numeratorGenerator u (addNumeratorExponent a i) (n + 1) -
          numeratorGenerator u (addNumeratorExponent a 5) (n + 1)) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [DSix_last]
    simp
  · rw [DSix_castSucc, actualD_numeratorGenerator]
    simp

theorem Dik_numeratorGenerator {R : Type*} [CommRing R] (u : R)
    (i k : Fin 6) (a : Fin 6 → ℕ) (n : ℕ) :
    Dik u i k (numeratorGenerator u a n) =
      ((a i : ActualRing u) - (a k : ActualRing u)) * numeratorGenerator u a n +
        algebraMap R (ActualRing u) u *
        (numeratorGenerator u (addNumeratorExponent a i) (n + 1) -
          numeratorGenerator u (addNumeratorExponent a k) (n + 1)) := by
  rw [Dik, Derivation.sub_apply, DSix_numeratorGenerator, DSix_numeratorGenerator]
  ring

theorem sum_Dik_numeratorGenerator {R : Type*} [CommRing R] (u : R)
    (i : Fin 6) (a : Fin 6 → ℕ) (n : ℕ) :
    (∑ k : Fin 6, Dik u i k (numeratorGenerator u a n)) =
      (6 * (a i : ActualRing u) - ∑ k : Fin 6, (a k : ActualRing u)) *
        numeratorGenerator u a n + algebraMap R (ActualRing u) u *
        (6 * numeratorGenerator u (addNumeratorExponent a i) (n + 1) -
          ∑ k : Fin 6, numeratorGenerator u (addNumeratorExponent a k) (n + 1)) := by
  simp only [Dik_numeratorGenerator, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem numeratorGenerator_pole_relation {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (n : ℕ) :
    (n + 1 : ActualRing u) * numeratorGenerator u a n =
      numeratorGenerator u a (n + 1) - algebraMap R (ActualRing u) u *
        ∑ i : Fin 6, numeratorGenerator u (addNumeratorExponent a i) (n + 1) := by
  have h := congrArg (fun x : ActualRing u => actualMonomial u (fun k => (a k : ℤ)) * x)
    (factorialPole_pole_relation u n)
  simp only [mul_sub, ← mul_assoc, numeratorGenerator_add, Finset.mul_sum] at h ⊢
  simpa only [numeratorGenerator, mul_assoc, mul_left_comm] using h

/-- The printed integral numerator reduction before dividing by the unit `6u`. -/
theorem numeratorReduction_identity {R : Type*} [CommRing R] (u : R)
    (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) :
    6 * algebraMap R (ActualRing u) u *
      numeratorGenerator u (addNumeratorExponent a i) (n + 1) =
        numeratorGenerator u a (n + 1) -
          ((n + 1 : ActualRing u) + 6 * (a i : ActualRing u) -
            ∑ k : Fin 6, (a k : ActualRing u)) * numeratorGenerator u a n +
          ∑ k : Fin 6, Dik u i k (numeratorGenerator u a n) := by
  rw [sum_Dik_numeratorGenerator]
  have h := numeratorGenerator_pole_relation u a n
  linear_combination h

theorem DSix_preserves_closed {R : Type*} [CommRing R] (u : R)
    (i : Fin 6) {g : ActualRing u} (hg : g ∈ FClosed u) : DSix u i g ∈ FClosed u := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [DSix_last]
    simp
  · rw [DSix_castSucc]
    exact actualD_preserves_closed u j hg

theorem Dik_preserves_closed {R : Type*} [CommRing R] (u : R)
    (i k : Fin 6) {g : ActualRing u} (hg : g ∈ FClosed u) : Dik u i k g ∈ FClosed u := by
  rw [Dik, Derivation.sub_apply]
  exact (FClosed u).sub_mem (DSix_preserves_closed u i hg) (DSix_preserves_closed u k hg)

def DSixClosed {R : Type*} [CommRing R] (u : R) (i : Fin 6) :
    FClosed u →ₗ[R] FClosed u := Fin.lastCases 0 (DClosed u) i

@[simp] theorem DSixClosed_last {R : Type*} [CommRing R] (u : R) :
    DSixClosed u (Fin.last 5) = 0 := Fin.lastCases_last

theorem DSixClosed_coe {R : Type*} [CommRing R] (u : R) (i : Fin 6) (g : FClosed u) :
    (DSixClosed u i g : ActualRing u) = DSix u i g := by
  refine Fin.lastCases (motive := fun j =>
    (DSixClosed u j g : ActualRing u) = DSix u j g) ?_ (fun j => ?_) i
  · rw [DSixClosed_last, DSix_last]
    rfl
  · simp only [DSixClosed, Fin.lastCases_castSucc, DSix_castSucc]
    rfl

def DikClosed {R : Type*} [CommRing R] (u : R) (i k : Fin 6) :
    FClosed u →ₗ[R] FClosed u := DSixClosed u i - DSixClosed u k

theorem DikClosed_coe {R : Type*} [CommRing R] (u : R) (i k : Fin 6) (g : FClosed u) :
    (DikClosed u i k g : ActualRing u) = Dik u i k g := by
  simp [DikClosed, Dik, DSixClosed_coe]

theorem DSixClosed_mem_exact {R : Type*} [CommRing R] (u : R)
    (i : Fin 6) (g : FClosed u) : DSixClosed u i g ∈ exactSubmodule u := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [DSixClosed_last]
    exact (exactSubmodule u).zero_mem
  · simpa only [DSixClosed, Fin.lastCases_castSucc] using DClosed_mem_exact u j g

theorem DikClosed_mem_exact {R : Type*} [CommRing R] (u : R)
    (i k : Fin 6) (g : FClosed u) : DikClosed u i k g ∈ exactSubmodule u := by
  exact (exactSubmodule u).sub_mem (DSixClosed_mem_exact u i g) (DSixClosed_mem_exact u k g)

theorem numeratorReduction_normalized {R : Type*} [CommRing R] (u v : R)
    (huv : v * (6 * u) = 1) (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) :
    numeratorGenerator u (addNumeratorExponent a i) (n + 1) =
      algebraMap R (ActualRing u) v *
        (numeratorGenerator u a (n + 1) -
          ((n + 1 : ActualRing u) + 6 * (a i : ActualRing u) -
            ∑ k : Fin 6, (a k : ActualRing u)) * numeratorGenerator u a n) +
      algebraMap R (ActualRing u) v * ∑ k : Fin 6, Dik u i k (numeratorGenerator u a n) := by
  have hunit : algebraMap R (ActualRing u) v * (6 * algebraMap R (ActualRing u) u) = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap R (ActualRing u)) huv
  calc
    _ = 1 * numeratorGenerator u (addNumeratorExponent a i) (n + 1) := (one_mul _).symm
    _ = algebraMap R (ActualRing u) v *
        (6 * algebraMap R (ActualRing u) u *
          numeratorGenerator u (addNumeratorExponent a i) (n + 1)) := by rw [← mul_assoc, hunit]
    _ = _ := by rw [numeratorReduction_identity]; ring

/-- All discarded primitives in the printed reduction are actually allowed. -/
theorem numeratorReduction_primitive_exact {R : Type*} [CommRing R] (u v : R)
    (a : Fin 6 → ℕ) (i : Fin 6) (n : ℕ) (ha : (∑ k, a k) ≤ n + 1) :
    v • (∑ k : Fin 6, DikClosed u i k
      ⟨numeratorGenerator u a n, numeratorGenerator_mem_closed u a n ha⟩) ∈ exactSubmodule u := by
  apply (exactSubmodule u).smul_mem
  exact (exactSubmodule u).sum_mem (fun k _ => DikClosed_mem_exact u i k _)

end

end WPResidueQuotient
