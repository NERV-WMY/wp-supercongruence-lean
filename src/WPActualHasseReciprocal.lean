import WPHasseReciprocity

open scoped Polynomial LaurentPolynomial
open Polynomial WPActualNativeHasse WPHasseIntegralTransport WPHasseReciprocity

namespace WPActualHasseReciprocal

theorem actual_half_exponent (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * ((p - 1) / 2) + 1 = p := by
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hodd with ⟨k, hk⟩
  omega

theorem actual_half_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    2 * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
  have h := congrArg (fun n : ℕ => (n : ZMod p)) (actual_half_exponent p hp)
  simpa using h

theorem actual_two_field_unit (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  rw [ne_eq, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
  intro hd
  have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
  omega

/-- Fixed-degree reflection evaluated at any nonzero point, including both literal endpoints. -/
theorem eval_reflect {K : Type*} [Field K] (N : ℕ) (P : K[X])
    (hdegree : P.natDegree ≤ N) (a : K) (ha : a ≠ 0) :
    (P.reflect N).eval a = a ^ N * P.eval a⁻¹ := by
  refine induction_with_natDegree_le
    (fun P => (P.reflect N).eval a = a ^ N * P.eval a⁻¹) N ?_ ?_ ?_ P hdegree
  · simp
  · intro n c _ hn
    rw [reflect_C_mul_X_pow, revAt_le hn]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [pow_sub₀ a ha hn]
    simp only [inv_pow]
    ring
  · intro A B _ _ hA hB
    rw [reflect_add, eval_add, hA, hB, eval_add, mul_add]

theorem actual_four_half_power (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (4 : ZMod p) ^ ((p - 1) / 2) = 1 := by
  rw [show (4 : ZMod p) = 2 ^ 2 by norm_num, ← pow_mul]
  have h : 2 * ((p - 1) / 2) = p - 1 := by have := actual_half_exponent p hp; omega
  rw [h]
  exact ZMod.pow_card_sub_one_eq_one (actual_two_field_unit p hp)

theorem actual_native_V_inverse_endpoint (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((nativeField p (p / 6)).comp (fieldV p)).eval ((4 : ZMod p)⁻¹) = 1 := by
  rw [Polynomial.eval_comp]
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 (actual_two_field_unit p hp)
  have hV : (fieldV p).eval ((4 : ZMod p)⁻¹) = 0 := by
    simp only [fieldV, eval_mul, eval_C, eval_pow, eval_sub, eval_ofNat, eval_one, eval_X]
    rw [mul_inv_cancel₀ h4, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]
  rw [hV, actual_native_field_origin]

/-- Actual native Hasse reciprocity, with its original source and endpoint normalization. -/
theorem actual_native_Hasse_reciprocal (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeField p (p / 6)).comp (fieldV p) =
      ((nativeField p (p / 6)).comp (fieldV p)).reflect ((p - 1) / 2) := by
  let P := (nativeField p (p / 6)).comp (fieldV p)
  let N := (p - 1) / 2
  have hdeg : P.natDegree ≤ N := actual_native_V_degree p hp
  have hrefdeg : (P.reflect N).natDegree ≤ N :=
    natDegree_reflect_le.trans (max_le (le_refl _) hdeg)
  have hNlt : N < p := by dsimp [N]; omega
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 (actual_two_field_unit p hp)
  apply WPFiniteHasseUniqueness.actual_finite_cubic_unique p hp P (P.reflect N)
    (hdeg.trans_lt hNlt) (hrefdeg.trans_lt hNlt)
  · rw [actual_native_V_endpoint, eval_reflect N P hdeg 4 h4,
      actual_native_V_inverse_endpoint p hp, actual_four_half_power p hp, mul_one]
  · exact actual_native_V_cubic_ODE p hp
  · exact actual_cubic_reciprocal_solution N (actual_two_field_unit p hp)
      (actual_half_field p hp) P hdeg (actual_native_V_cubic_ODE p hp)

/-- Fixed-degree polynomial reflection is the entire Laurent reciprocal, coefficient by coefficient. -/
theorem toLaurent_reflect {K : Type*} [CommRing K] (N : ℕ) (P : K[X])
    (hdegree : P.natDegree ≤ N) :
    Polynomial.toLaurent (P.reflect N) =
      LaurentPolynomial.T (N : ℤ) * LaurentPolynomial.invert (Polynomial.toLaurent P) := by
  refine induction_with_natDegree_le
    (fun P => Polynomial.toLaurent (P.reflect N) =
      LaurentPolynomial.T (N : ℤ) * LaurentPolynomial.invert (Polynomial.toLaurent P))
    N ?_ ?_ ?_ P hdegree
  · simp
  · intro n c _ hn
    rw [reflect_C_mul_X_pow, revAt_le hn]
    simp only [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      LaurentPolynomial.T_pow, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
      mul_one]
    have hcast : ((N - n : ℕ) : ℤ) = (N : ℤ) + -(n : ℤ) := by omega
    rw [hcast, LaurentPolynomial.T_add]
    ring
  · intro A B _ _ hA hB
    rw [reflect_add, map_add, hA, hB, map_add, map_add, mul_add]

theorem actual_native_Hasse_Laurent (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    Polynomial.toLaurent ((nativeField p (p / 6)).comp (fieldV p)) =
      LaurentPolynomial.T (((p - 1) / 2 : ℕ) : ℤ) *
        LaurentPolynomial.invert (Polynomial.toLaurent ((nativeField p (p / 6)).comp (fieldV p))) := by
  conv_lhs => rw [actual_native_Hasse_reciprocal p hp]
  exact toLaurent_reflect _ _ (actual_native_V_degree p hp)

end WPActualHasseReciprocal
