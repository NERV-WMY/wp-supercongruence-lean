import WPFiniteFifthSourceContraction
import Mathlib.Algebra.Polynomial.Laurent

open scoped Polynomial LaurentPolynomial

namespace WPFiniteJCarrier

open WPFiniteJSource WPFiniteJNormalization WPFiniteJHighCoefficient

variable {K : Type*} [Field K]

/-- Original JT2a full Laurent carrier, including its reflected and third positive bands. -/
noncomputable def GJ (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (17 / 45 : K) * LaurentPolynomial.T 0 *
      ((HJP p).toLaurent + LaurentPolynomial.invert (HJP p).toLaurent) -
    LaurentPolynomial.C (4 / 45 : K) * LaurentPolynomial.T (p : ℤ) *
      ((HJP p).toLaurent + LaurentPolynomial.invert (HJP p).toLaurent) -
    LaurentPolynomial.C (4 / 45 : K) * LaurentPolynomial.T (-(p : ℤ)) *
      ((HJP p).toLaurent + LaurentPolynomial.invert (HJP p).toLaurent)

theorem shifted_coeff (a : K) (n m : ℤ) (P : K[T;T⁻¹]) :
    (LaurentPolynomial.C a * LaurentPolynomial.T n * P).coeff m = a * P.coeff (m - n) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single_mul_apply]
  congr 1
  congr 1
  omega

theorem toLaurent_coeff_nat (P : K[X]) (n : ℕ) : P.toLaurent.coeff (n : ℤ) = P.coeff n := by
  rw [LaurentPolynomial.coeff_toLaurent]
  have h := Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective P.toFinsupp.coeff n
  simpa only [Nat.castEmbedding_apply, Polynomial.toFinsupp_apply] using h

theorem toLaurent_coeff_outside (P : K[X]) (j : ℤ)
    (hj : j < 0 ∨ (P.natDegree : ℤ) < j) : P.toLaurent.coeff j = 0 := by
  by_contra h
  have hm : j ∈ P.toLaurent.coeff.support := Finsupp.mem_support_iff.mpr h
  rw [LaurentPolynomial.support_coeff_toLaurent] at hm
  obtain ⟨n, hn, hnj⟩ := Finset.mem_map.mp hm
  have hnle : n ≤ P.natDegree := Polynomial.le_natDegree_of_mem_supp n hn
  change (n : ℤ) = j at hnj
  rcases hj with hj | hj <;> omega

theorem GJ_coefficient (p : ℕ) (m : ℤ) : (GJ p : K[T;T⁻¹]).coeff m =
    (17 / 45 : K) * ((HJP p).toLaurent.coeff m + (HJP p).toLaurent.coeff (-m)) -
      (4 / 45 : K) * ((HJP p).toLaurent.coeff (m - p) + (HJP p).toLaurent.coeff (-(m - p))) -
      (4 / 45 : K) * ((HJP p).toLaurent.coeff (m + p) + (HJP p).toLaurent.coeff (-(m + p))) := by
  simp only [GJ, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, shifted_coeff,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply, LaurentPolynomial.invert_apply, sub_zero, sub_neg_eq_add]

theorem actual_GJ_2p_coefficient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (GJ p : K[T;T⁻¹]).coeff (2 * (p : ℤ)) = -4 * (HJP p : K[X]).coeff p / 45 := by
  have hdeg := HJP_natDegree_le (K := K) p hp
  have h2 : (HJP p : K[X]).toLaurent.coeff (2 * (p : ℤ)) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hn2 : (HJP p : K[X]).toLaurent.coeff (-(2 * (p : ℤ))) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have h3 : (HJP p : K[X]).toLaurent.coeff (3 * (p : ℤ)) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hn3 : (HJP p : K[X]).toLaurent.coeff (-(3 * (p : ℤ))) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hn1 : (HJP p : K[X]).toLaurent.coeff (-(p : ℤ)) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inl (by omega))
  rw [GJ_coefficient, show (2 * (p : ℤ)) - p = p by ring,
    show (2 * (p : ℤ)) + p = 3 * p by ring, h2, hn2, h3, hn3, hn1, toLaurent_coeff_nat]
  ring

theorem actual_GJ_fifth_phase (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    (GJ p : K[T;T⁻¹]).coeff (2 * (p : ℤ)) = -4 * U_J p u / 225 := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  have h45 : (45 : K) ≠ 0 := by rw [show (45 : K) = 3 ^ 2 * 5 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) h5
  have h225 : (225 : K) ≠ 0 := by rw [show (225 : K) = 3 ^ 2 * 5 ^ 2 by ring]; exact mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h5)
  rw [actual_GJ_2p_coefficient p hp, actual_J_high_coefficient p hp u hu]
  field_simp [h5, h45, h225]
  ring

end WPFiniteJCarrier
