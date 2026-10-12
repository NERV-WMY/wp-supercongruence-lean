import WPFieldAssembly.ActualBpairLowHConicPrimitive
import WPFieldAssembly.ActualBpairLowHQuadratic
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The entire odd quotient is contracted only after removing its literal factor X. -/
noncomputable def lowHOddHalfP (P : K[X]) : K[X] := P.divX.contract 2

theorem lowHOddHalfP_coeff (P : K[X]) (n : ℕ) :
    (lowHOddHalfP P).coeff n = P.coeff (2 * n + 1) := by
  rw [lowHOddHalfP, coeff_contract (by decide : 2 ≠ 0), coeff_divX, Nat.mul_comm]

theorem lowHOddHalfP_expand (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    expand K 2 (lowHOddHalfP P) = P.divX := by
  ext n
  rw [coeff_expand (by decide : 0 < 2), lowHOddHalfP, coeff_contract (by decide : 2 ≠ 0)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, Nat.div_mul_cancel hn]
  · rw [if_neg hn, coeff_divX]
    have hn0 : n % 2 ≠ 0 := by intro h; exact hn (Nat.dvd_of_mod_eq_zero h)
    exact (hodd (n + 1) (by omega)).symm

theorem lowHOddHalfP_source (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    P = X * (lowHOddHalfP P).comp (X ^ 2) := by
  rw [← expand_eq_comp_X_pow, lowHOddHalfP_expand P hodd]
  have he := X_mul_divX_add P
  rw [hodd 0 (by decide), map_zero, add_zero] at he
  exact he.symm

theorem lowHOddHalfP_degree (P : K[X]) :
    (lowHOddHalfP P).natDegree ≤ (P.natDegree - 1) / 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [lowHOddHalfP, coeff_contract (by decide : 2 ≠ 0)]
  apply coeff_eq_zero_of_natDegree_lt
  rw [natDegree_divX_eq_natDegree_tsub_one]
  omega

/-- In the local w coordinate the original P(t)*w*dt becomes this whole polynomial. -/
noncomputable def lowHConicLocalP (P : K[X]) : K[X] :=
  Polynomial.C (1 / 5 : K) * X ^ 2 *
    (lowHOddHalfP P).comp (Polynomial.C (1 / 5 : K) * (1 + X ^ 2))

theorem lowHConicLocalP_even (P : K[X]) :
    (lowHConicLocalP P).comp (-X) = lowHConicLocalP P := by
  simp only [lowHConicLocalP, mul_comp, C_comp, pow_comp, X_comp, neg_sq,
    comp_assoc, add_comp, one_comp]

theorem lowHConicLocalP_degree (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    (lowHConicLocalP P).natDegree ≤ P.natDegree + 1 := by
  by_cases hp0 : P = 0
  · subst P
    simp [lowHConicLocalP, lowHOddHalfP, contract]
  · have hpdeg : 1 ≤ P.natDegree := by
      by_contra h
      have he := eq_C_of_natDegree_eq_zero (show P.natDegree = 0 by omega)
      rw [hodd 0 (by decide), map_zero] at he
      exact hp0 he
    have hu : (Polynomial.C (1 / 5 : K) * (1 + X ^ 2)).natDegree ≤ 2 := by
      apply (natDegree_C_mul_le _ _).trans
      exact (natDegree_add_le _ _).trans (by simp)
    have hc : ((lowHOddHalfP P).comp (Polynomial.C (1 / 5 : K) * (1 + X ^ 2))).natDegree ≤
        ((P.natDegree - 1) / 2) * 2 :=
      natDegree_comp_le.trans (Nat.mul_le_mul (lowHOddHalfP_degree P) hu)
    have hx : (Polynomial.C (1 / 5 : K) * (X : K[X]) ^ 2).natDegree ≤ 2 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    have he : (lowHConicLocalP P).natDegree ≤ 2 + ((P.natDegree - 1) / 2) * 2 :=
      natDegree_mul_le.trans (Nat.add_le_add hx hc)
    omega

private theorem lowH_conic_half_unit (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (2 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 2 : K) = 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have he := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (mul_one_div_cancel h2)
  simpa only [map_mul, map_ofNat, map_one] using he

theorem lowHConic_relation (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : K[T;T⁻¹]) * (lowHConicT η) ^ 2 = lowHConicW ^ 2 + 1 := by
  have hηC := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hη
  simp only [map_mul, map_pow, map_ofNat, map_one] at hηC
  have h2C := lowH_conic_half_unit (K := K) p hp
  have hAB : (T 1 : K[T;T⁻¹]) * T (-1) = 1 := by rw [← T_add]; rfl
  have hdiv : LaurentPolynomial.C (η / 2) =
      LaurentPolynomial.C η * LaurentPolynomial.C (1 / 2 : K) := by
    simp only [div_eq_mul_inv, one_mul, map_mul]
  rw [lowHConicT, lowHConicW, hdiv]
  linear_combination (LaurentPolynomial.C (1 / 2 : K)) ^ 2 * (T 1 + T (-1)) ^ 2 * hηC +
    4 * (LaurentPolynomial.C (1 / 2 : K)) ^ 2 * hAB +
    (2 * LaurentPolynomial.C (1 / 2 : K) + 1) * h2C

theorem lowHConic_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (5 : K[T;T⁻¹]) * lowHConicT η * D (lowHConicT η) = lowHConicW * D lowHConicW := by
  have ht : D ((lowHConicT η) ^ 2) = 2 * lowHConicT η * D (lowHConicT η) := by
    rw [pow_two, D_mul]
    ring
  have hw : D ((lowHConicW : K[T;T⁻¹]) ^ 2) = 2 * lowHConicW * D lowHConicW := by
    rw [pow_two, D_mul]
    ring
  have h5 : D (5 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (5 : K)
  have h1 : D (1 : K[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : K)
  have he := congrArg D (lowHConic_relation p hp η hη)
  rw [D_mul, h5, zero_mul, zero_add, ht, map_add, hw, h1, add_zero] at he
  have h2C := lowH_conic_half_unit (K := K) p hp
  linear_combination LaurentPolynomial.C (1 / 2 : K) * he -
    (5 * lowHConicT η * D (lowHConicT η) - lowHConicW * D lowHConicW) * h2C

theorem lowHConic_square_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (η : K) (hη : (5 : K) * η ^ 2 = 1) :
    (lowHConicT η) ^ 2 = LaurentPolynomial.C (1 / 5 : K) * (1 + lowHConicW ^ 2) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (mul_one_div_cancel h5)
  simp only [map_mul, map_ofNat, map_one] at hc
  have he := lowHConic_relation p hp η hη
  linear_combination LaurentPolynomial.C (1 / 5 : K) * he - (lowHConicT η) ^ 2 * hc

/-- This exact source identity retains the original conic differential before local residue extraction. -/
theorem lowHConicPullback_local_source (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (η : K) (hη : (5 : K) * η ^ 2 = 1) (P : K[X])
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    lowHConicPullback η P = Polynomial.eval₂ LaurentPolynomial.C lowHConicW (lowHConicLocalP P) *
      D lowHConicW := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hc := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) (mul_one_div_cancel h5)
  simp only [map_mul, map_ofNat, map_one] at hc
  have ht := lowHConic_cleared_derivative p hp η hη
  have he := congrArg (fun Q : K[X] => Polynomial.eval₂ LaurentPolynomial.C (lowHConicT η) Q)
    (lowHOddHalfP_source P hodd)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow] at he
  simp only [lowHConicPullback, he, lowHConicLocalP, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_comp, Polynomial.eval₂_add,
    Polynomial.eval₂_one]
  rw [← lowHConic_square_source p hp η hη]
  linear_combination LaurentPolynomial.C (1 / 5 : K) * lowHConicW *
    Polynomial.eval₂ LaurentPolynomial.C ((lowHConicT η) ^ 2) (lowHOddHalfP P) * ht -
    lowHConicT η * lowHConicW * D (lowHConicT η) *
      Polynomial.eval₂ LaurentPolynomial.C ((lowHConicT η) ^ 2) (lowHOddHalfP P) * hc

/-- The retained w^-p band has zero residue from the actual local polynomial bound. -/
theorem lowHConicLocal_phase_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (n : ℤ) :
    (T (n * (p : ℤ)) * (lowHConicLocalP P).toLaurent).coeff (-1) = 0 := by
  exact lowH_subp_frobenius_phase_zero p hp _
    (by have := lowHConicLocalP_degree P hodd; omega) n

theorem lowHConicLocal_primitive (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    D (lowHUnitLaurentPrimitive (lowHConicLocalP P).toLaurent) = (lowHConicLocalP P).toLaurent := by
  have hd := lowHConicLocalP_degree P hodd
  apply lowH_signed_band_primitive p
  · intro j hj
    rcases hj with hj | hj
    · exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
    · exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  · exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))

/-- The full local numerator and every signed denominator-p band remain inside exactness. -/
theorem lowHConicLocal_full_frobenius_zero (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (Q : K[T;T⁻¹]) (n : ℤ) :
    (T (n * (p : ℤ)) * Q ^ p * (lowHConicLocalP P).toLaurent).coeff (-1) = 0 := by
  have hnp : (p : ℤ) ∣ n * (p : ℤ) := ⟨n, by ring⟩
  have he : D (T (n * (p : ℤ)) *
      (Q ^ p * lowHUnitLaurentPrimitive (lowHConicLocalP P).toLaurent)) =
      T (n * (p : ℤ)) * (Q ^ p * (lowHConicLocalP P).toLaurent) := by
    rw [D_frobenius_shift p _ _ hnp, D_mul, lowH_D_frobenius, zero_mul, zero_add,
      lowHConicLocal_primitive p hp P hdeg hodd]
  rw [mul_assoc, ← he]
  exact lowH_derivative_residue _

end WPFieldAssembly.ActualBpairContraction
