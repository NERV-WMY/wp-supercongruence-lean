import WPFiniteLaurentDifferential

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

/-- A primitive of the complete Laurent support, using the original exponent pivots. -/
noncomputable def lowHUnitLaurentPrimitive : K[T;T⁻¹] →ₗ[K] K[T;T⁻¹] :=
  (Finsupp.linearCombination K (fun n : ℤ =>
    C (((n + 1 : ℤ) : K)⁻¹) * T (n + 1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

theorem lowHUnitLaurentPrimitive_monomial (a : K) (n : ℤ) :
    lowHUnitLaurentPrimitive (C a * T n) = C (a / ((n + 1 : ℤ) : K)) * T (n + 1) := by
  rw [← single_eq_C_mul_T]
  change Finsupp.linearCombination K _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, smul_eq_C_mul, ← mul_assoc, ← map_mul]
  simp only [div_eq_mul_inv]

private theorem lowH_monomial_coeff (a : K) (n j : ℤ) :
    (C a * T n).coeff j = if n = j then a else 0 := by
  rw [← single_eq_C_mul_T]
  exact Finsupp.single_apply

theorem lowHUnitLaurentPrimitive_coeff (P : K[T;T⁻¹]) (j : ℤ) :
    (lowHUnitLaurentPrimitive P).coeff j = P.coeff (j - 1) / (j : K) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]
    ring
  | C_mul_T n a =>
    rw [lowHUnitLaurentPrimitive_monomial, lowH_monomial_coeff, lowH_monomial_coeff]
    by_cases hn : n = j - 1
    · subst n
      rw [sub_add_cancel, if_pos rfl, if_pos rfl]
    · rw [if_neg hn, if_neg (by omega : n + 1 ≠ j), zero_div]

/-- A source with genuine unit pivots has an exact full Laurent primitive. -/
theorem lowHUnitLaurentPrimitive_source (P : K[T;T⁻¹])
    (hunit : ∀ j : ℤ, P.coeff j ≠ 0 → ((j + 1 : ℤ) : K) ≠ 0) :
    D (lowHUnitLaurentPrimitive P) = P := by
  ext j
  rw [D_coeff, lowHUnitLaurentPrimitive_coeff, show j + 1 - 1 = j by omega]
  by_cases hj : P.coeff j = 0
  · rw [hj, zero_div, mul_zero]
  · rw [div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ (hunit j hj), mul_one]

/-- The entire signed sub-p band has unit pivots once the actual residue is zero. -/
theorem lowH_signed_band_unit (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : K[T;T⁻¹])
    (hband : ∀ j : ℤ, j + 1 ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j + 1 → P.coeff j = 0)
    (hres : P.coeff (-1) = 0) (j : ℤ) (hj : P.coeff j ≠ 0) :
    ((j + 1 : ℤ) : K) ≠ 0 := by
  have hb : -(p : ℤ) < j + 1 ∧ j + 1 < p := by
    constructor
    · by_contra h
      exact hj (hband j (Or.inl (by omega)))
    · by_contra h
      exact hj (hband j (Or.inr (by omega)))
  have hj0 : j + 1 ≠ 0 := by
    intro h
    have he : j = -1 := by omega
    subst j
    exact hj hres
  by_cases hpos : 0 < j + 1
  · exact integer_unit_in_band p (j + 1) ⟨hpos, hb.2⟩
  · have hu := integer_unit_in_band (K := K) p (-(j + 1)) (by omega)
    rw [Int.cast_neg] at hu
    exact neg_ne_zero.mp hu

/-- This is the finite primitive criterion used on the full conic parameter source. -/
theorem lowH_signed_band_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : K[T;T⁻¹])
    (hband : ∀ j : ℤ, j + 1 ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j + 1 → P.coeff j = 0)
    (hres : P.coeff (-1) = 0) : D (lowHUnitLaurentPrimitive P) = P := by
  exact lowHUnitLaurentPrimitive_source P (lowH_signed_band_unit p P hband hres)

private theorem lowH_D_pow_succ (Q : K[T;T⁻¹]) (n : ℕ) :
    D (Q ^ (n + 1)) = C ((n + 1 : ℕ) : K) * Q ^ n * D Q := by
  induction n with
  | zero => simp only [Nat.zero_add, pow_one, Nat.cast_one, map_one, pow_zero, one_mul]
  | succ n hn =>
    rw [pow_succ, D_mul, hn, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem lowH_D_frobenius (p : ℕ) [Fact p.Prime] [CharP K p] (Q : K[T;T⁻¹]) :
    D (Q ^ p) = 0 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have he := lowH_D_pow_succ Q (p - 1)
  rw [Nat.sub_add_cancel hp, CharP.cast_eq_zero K p, map_zero, zero_mul, zero_mul] at he
  exact he

theorem lowH_derivative_residue (P : K[T;T⁻¹]) : (D P).coeff (-1) = 0 := by
  rw [D_coeff]
  simp only [neg_add_cancel, Int.cast_zero, zero_mul]

/-- Every full Frobenius multiplier preserves exactness and hence zero residue. -/
theorem lowH_conic_frobenius_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (P Q : K[T;T⁻¹])
    (hband : ∀ j : ℤ, j + 1 ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j + 1 → P.coeff j = 0)
    (hres : P.coeff (-1) = 0) : (Q ^ p * P).coeff (-1) = 0 := by
  have he : D (Q ^ p * lowHUnitLaurentPrimitive P) = Q ^ p * P := by
    rw [D_mul, lowH_D_frobenius, zero_mul, zero_add, lowH_signed_band_primitive p P hband hres]
  rw [← he]
  exact lowH_derivative_residue _

/-- A parity condition on every exponent of the full Laurent source. -/
def lowHLaurentParity (P : K[T;T⁻¹]) (r : ℤ) : Prop :=
  ∀ j : ℤ, j % 2 ≠ r % 2 → P.coeff j = 0

private theorem lowH_parity_monomial (a : K) (n : ℤ) :
    lowHLaurentParity (C a * T n) n := by
  intro j hj
  rw [lowH_monomial_coeff, if_neg (by intro he; exact hj (by omega))]

private theorem lowH_parity_add {P Q : K[T;T⁻¹]} {r : ℤ}
    (hP : lowHLaurentParity P r) (hQ : lowHLaurentParity Q r) :
    lowHLaurentParity (P + Q) r := by
  intro j hj
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP j hj, hQ j hj, add_zero]

private theorem lowH_parity_sub {P Q : K[T;T⁻¹]} {r : ℤ}
    (hP : lowHLaurentParity P r) (hQ : lowHLaurentParity Q r) :
    lowHLaurentParity (P - Q) r := by
  intro j hj
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hP j hj, hQ j hj, sub_self]

private theorem lowH_parity_mul {P Q : K[T;T⁻¹]} {r s : ℤ}
    (hP : lowHLaurentParity P r) (hQ : lowHLaurentParity Q s) :
    lowHLaurentParity (P * Q) (r + s) := by
  classical
  intro j hj
  by_contra hz
  have hm : j ∈ (P * Q).coeff.support := Finsupp.mem_support_iff.mpr hz
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset P Q hm)
  have hi' : i % 2 = r % 2 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hi) (hP i h)
  have hk' : k % 2 = s % 2 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hQ k h)
  apply hj
  rw [← hik, Int.add_emod, hi', hk', ← Int.add_emod]

private theorem lowH_parity_C (a : K) : lowHLaurentParity (C a) 0 := by
  simpa only [T_zero, mul_one] using lowH_parity_monomial a 0

private theorem lowH_parity_pow {P : K[T;T⁻¹]} {r : ℤ}
    (hP : lowHLaurentParity P r) (n : ℕ) : lowHLaurentParity (P ^ n) ((n : ℤ) * r) := by
  induction n with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, map_one] using lowH_parity_C (1 : K)
  | succ n hn =>
    rw [pow_succ]
    have he := lowH_parity_mul hn hP
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using he

private theorem lowH_parity_D {P : K[T;T⁻¹]} {r : ℤ}
    (hP : lowHLaurentParity P r) : lowHLaurentParity (D P) (r - 1) := by
  intro j hj
  rw [D_coeff, hP (j + 1) (by omega), mul_zero]

private theorem lowH_parity_eval (P : K[X]) (U : K[T;T⁻¹])
    (hU : lowHLaurentParity U 1)
    (hP : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    lowHLaurentParity (Polynomial.eval₂ C U P) 1 := by
  classical
  rw [P.as_sum_support_C_mul_X_pow]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]
  intro j hj
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hn0 : P.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hnodd : n % 2 = 1 := by
    have he : n % 2 ≠ 0 := by intro h; exact hn0 (hP n h)
    omega
  have hnZ : (n : ℤ) % 2 = 1 := by omega
  have he := lowH_parity_mul (lowH_parity_C (P.coeff n)) (lowH_parity_pow hU n)
  exact he j (by omega)

/-- The full rational conic parameter, with both r and 1/r branches retained. -/
noncomputable def lowHConicT (η : K) : K[T;T⁻¹] := C (η / 2) * (T 1 + T (-1))

noncomputable def lowHConicW : K[T;T⁻¹] := C (1 / 2 : K) * (T 1 - T (-1))

/-- The entire odd source P(t)*w*dt in the original conic parameter. -/
noncomputable def lowHConicPullback (η : K) (P : K[X]) : K[T;T⁻¹] :=
  Polynomial.eval₂ C (lowHConicT η) P * lowHConicW * D (lowHConicT η)

private theorem lowH_conic_t_parity (η : K) : lowHLaurentParity (lowHConicT η) 1 := by
  have hn : lowHLaurentParity (T (-1) : K[T;T⁻¹]) 1 := by
    simpa [lowHLaurentParity] using lowH_parity_monomial (1 : K) (-1)
  have hp : lowHLaurentParity (T 1 : K[T;T⁻¹]) 1 := by
    simpa only [map_one, one_mul] using lowH_parity_monomial (1 : K) 1
  exact lowH_parity_mul (lowH_parity_C (η / 2)) (lowH_parity_add hp hn)

private theorem lowH_conic_w_parity : lowHLaurentParity (lowHConicW : K[T;T⁻¹]) 1 := by
  have hn : lowHLaurentParity (T (-1) : K[T;T⁻¹]) 1 := by
    simpa [lowHLaurentParity] using lowH_parity_monomial (1 : K) (-1)
  have hp : lowHLaurentParity (T 1 : K[T;T⁻¹]) 1 := by
    simpa only [map_one, one_mul] using lowH_parity_monomial (1 : K) 1
  exact lowH_parity_mul (lowH_parity_C (1 / 2 : K)) (lowH_parity_sub hp hn)

theorem lowHConicPullback_parity (η : K) (P : K[X])
    (hP : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    lowHLaurentParity (lowHConicPullback η P) 0 := by
  have ht := lowH_conic_t_parity η
  have he := lowH_parity_mul
    (lowH_parity_mul (lowH_parity_eval P (lowHConicT η) ht hP) lowH_conic_w_parity)
    (lowH_parity_D ht)
  exact he

theorem lowHConicPullback_residue (η : K) (P : K[X])
    (hP : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    (lowHConicPullback η P).coeff (-1) = 0 :=
  lowHConicPullback_parity η P hP (-1) (by decide)

private theorem lowH_eval₂_above (P : K[X]) (U : K[T;T⁻¹]) (hU : Above U 1) :
    Above (Polynomial.eval₂ C U P) (P.natDegree : ℤ) := by
  classical
  have hex := congrArg (fun Q : K[X] => Polynomial.eval₂ C U Q) P.as_sum_support_C_mul_X_pow
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.eval₂_X] at hex
  rw [hex]
  intro j hj
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := Polynomial.le_natDegree_of_mem_supp n hn
  have he := Above_C_mul (Above_pow hU n) (P.coeff n)
  exact he j (by simp only [mul_one]; omega)

private theorem lowH_invert_eval₂ (P : K[X]) (U : K[T;T⁻¹]) :
    invert (Polynomial.eval₂ C U P) = Polynomial.eval₂ C (invert U) P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial n a => simp only [Polynomial.eval₂_monomial, map_mul, invert_C, map_pow]

private theorem lowH_conic_t_above (η : K) : Above (lowHConicT η) 1 := by
  have hp : Above (T 1 : K[T;T⁻¹]) 1 := by
    simpa only [map_one, one_mul] using Above_monomial (1 : K) 1
  have hn : Above (T (-1) : K[T;T⁻¹]) 1 := by
    apply Above_mono (b := 1) (a := -1) _ (by omega)
    simpa only [map_one, one_mul] using Above_monomial (1 : K) (-1)
  exact Above_C_mul (Above_add hp hn) _

private theorem lowH_conic_invert_t_above (η : K) : Above (invert (lowHConicT η)) 1 := by
  have he : invert (lowHConicT η) = lowHConicT η := by
    simp only [lowHConicT, map_mul, invert_C, map_add, invert_T, neg_neg]
    ring
  rw [he]
  exact lowH_conic_t_above η

private theorem lowH_conic_w_above : Above (lowHConicW : K[T;T⁻¹]) 1 := by
  have hp : Above (T 1 : K[T;T⁻¹]) 1 := by
    simpa only [map_one, one_mul] using Above_monomial (1 : K) 1
  have hn : Above (T (-1) : K[T;T⁻¹]) 1 := by
    apply Above_mono (b := 1) (a := -1) _ (by omega)
    simpa only [map_one, one_mul] using Above_monomial (1 : K) (-1)
  exact Above_C_mul (Above_sub hp hn) _

private theorem lowH_conic_invert_w_above : Above (invert (lowHConicW : K[T;T⁻¹])) 1 := by
  have he : invert (lowHConicW : K[T;T⁻¹]) = -lowHConicW := by
    simp only [lowHConicW, map_mul, invert_C, map_sub, invert_T, neg_neg]
    ring
  rw [he]
  exact Above_neg lowH_conic_w_above

theorem lowHConicPullback_upper (η : K) (P : K[X]) :
    Above (lowHConicPullback η P) ((P.natDegree : ℤ) + 1) := by
  have he := Above_mul
    (Above_mul (lowH_eval₂_above P _ (lowH_conic_t_above η)) lowH_conic_w_above)
    (Above_D (lowH_conic_t_above η))
  exact he

theorem lowHConicPullback_lower (η : K) (P : K[X]) :
    Above (invert (lowHConicPullback η P)) ((P.natDegree : ℤ) + 3) := by
  have hd : Above (invert (D (lowHConicT η))) 2 := by
    have he := Above_D (lowH_conic_invert_t_above η)
    rw [D_invert] at he
    intro j hj
    have hz := he (j - 2) (by omega)
    rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] at hz
    have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-2) (j - 2) (invert (D (lowHConicT η)))
    simp only [map_one, one_mul, sub_neg_eq_add, sub_add_cancel] at hs
    rw [hs] at hz
    exact neg_eq_zero.mp hz
  simp only [lowHConicPullback, map_mul, lowH_invert_eval₂]
  have he := Above_mul
    (Above_mul (lowH_eval₂_above P _ (lowH_conic_invert_t_above η)) lowH_conic_invert_w_above) hd
  convert he using 1
  ring

/-- All signed pivots of the original low-degree odd conic source are units. -/
theorem lowHConicPullback_band (p : ℕ) (hp : 19 ≤ p) (η : K) (P : K[X])
    (hP : P.natDegree ≤ p - 8) (j : ℤ)
    (hj : j + 1 ≤ -(p : ℤ) ∨ (p : ℤ) ≤ j + 1) :
    (lowHConicPullback η P).coeff j = 0 := by
  rcases hj with hj | hj
  · have he := lowHConicPullback_lower η P (-j) (by omega)
    simpa only [invert_apply, neg_neg] using he
  · exact lowHConicPullback_upper η P j (by omega)

/-- The full reciprocal conic source has a finite rational primitive in the parameter. -/
theorem lowHConicPullback_primitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) :
    D (lowHUnitLaurentPrimitive (lowHConicPullback η P)) = lowHConicPullback η P := by
  exact lowH_signed_band_primitive p _ (lowHConicPullback_band p hp η P hdeg)
    (lowHConicPullback_residue η P hodd)

theorem lowHConicPullback_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (η : K) (P : K[X]) (hdeg : P.natDegree ≤ p - 8)
    (hodd : ∀ n : ℕ, n % 2 = 0 → P.coeff n = 0) (Q : K[T;T⁻¹]) :
    (Q ^ p * lowHConicPullback η P).coeff (-1) = 0 := by
  exact lowH_conic_frobenius_residue p _ Q (lowHConicPullback_band p hp η P hdeg)
    (lowHConicPullback_residue η P hodd)

end WPFieldAssembly.ActualBpairContraction
