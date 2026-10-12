import WPHasseIntegralTransport

open scoped Polynomial
open Polynomial WPActualNativeHasse WPHasseCubicSource WPHasseIntegralTransport

namespace WPHasseReciprocity

noncomputable def cubicB3 {K : Type*} [CommRing K] : K[X] := cubicA3
noncomputable def cubicB2 {K : Type*} [CommRing K] : K[X] := X * cubicA2 - 3 * cubicA3
noncomputable def cubicB1 {K : Type*} [CommRing K] : K[X] :=
  X ^ 2 * cubicA1 - X * cubicA2 + 2 * cubicA3
noncomputable def cubicB0 {K : Type*} [CommRing K] : K[X] := X ^ 3 * cubicA0

noncomputable def indicialPolynomial {K : Type*} [CommRing K] (v : K) : K[X] :=
  cubicB3 * C (v ^ 3) + cubicB2 * C (v ^ 2) + cubicB1 * C v + cubicB0

/-- All six coefficients of the actual cubic Euler operator, over an arbitrary ring. -/
theorem actual_indicial_expansion {K : Type*} [CommRing K] (v : K) :
    indicialPolynomial v =
      C (128 * v ^ 3 - 384 * v ^ 2 + 256 * v) * X ^ 0 +
      C (-960 * v ^ 3 + 1440 * v ^ 2 - 480 * v) * X ^ 1 +
      C (1480 * v ^ 3 - 40 * v) * X ^ 2 +
      C (1480 * v ^ 3 + 2220 * v ^ 2 + 1070 * v + 165) * X ^ 3 +
      C (-960 * v ^ 3 - 2880 * v ^ 2 - 2640 * v - 720) * X ^ 4 +
      C (128 * v ^ 3 + 576 * v ^ 2 + 736 * v + 240) * X ^ 5 := by
  norm_num [indicialPolynomial, cubicB3, cubicB2, cubicB1, cubicB0, cubicA3, cubicA2,
    cubicA1, cubicA0, cubicDiscriminant, cubicNumerator, derivative_mul,
    derivative_pow_succ, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem indicial_degree {K : Type*} [CommRing K] (v : K) :
    (indicialPolynomial v).natDegree ≤ 5 := by
  rw [actual_indicial_expansion]
  compute_degree

/-- The exact reciprocal pairing; the only excluded characteristic is two. -/
theorem actual_indicial_reciprocal {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (v : K) :
    indicialPolynomial (-(1 / 2) - v) = -(indicialPolynomial v).reflect 5 := by
  rw [actual_indicial_expansion, actual_indicial_expansion]
  simp only [reflect_add, reflect_C_mul_X_pow]
  norm_num only [revAt_le, Nat.sub_self, Nat.sub_zero]
  have h0 : 128 * (-(1 / 2 : K) - v) ^ 3 - 384 * (-(1 / 2 : K) - v) ^ 2 +
      256 * (-(1 / 2 : K) - v) = -(128 * v ^ 3 + 576 * v ^ 2 + 736 * v + 240) := by
    field_simp
    ring
  have h1 : -960 * (-(1 / 2 : K) - v) ^ 3 + 1440 * (-(1 / 2 : K) - v) ^ 2 -
      480 * (-(1 / 2 : K) - v) = -(-960 * v ^ 3 - 2880 * v ^ 2 - 2640 * v - 720) := by
    field_simp
    ring
  have h2v : 1480 * (-(1 / 2 : K) - v) ^ 3 - 40 * (-(1 / 2 : K) - v) =
      -(1480 * v ^ 3 + 2220 * v ^ 2 + 1070 * v + 165) := by
    field_simp
    ring
  have h3 : 1480 * (-(1 / 2 : K) - v) ^ 3 + 2220 * (-(1 / 2 : K) - v) ^ 2 +
      1070 * (-(1 / 2 : K) - v) + 165 = -(1480 * v ^ 3 - 40 * v) := by
    field_simp
    ring
  have h4 : -960 * (-(1 / 2 : K) - v) ^ 3 - 2880 * (-(1 / 2 : K) - v) ^ 2 -
      2640 * (-(1 / 2 : K) - v) - 720 = -(-960 * v ^ 3 + 1440 * v ^ 2 - 480 * v) := by
    field_simp
    ring
  have h5 : 128 * (-(1 / 2 : K) - v) ^ 3 + 576 * (-(1 / 2 : K) - v) ^ 2 +
      736 * (-(1 / 2 : K) - v) + 240 = -(128 * v ^ 3 - 384 * v ^ 2 + 256 * v) := by
    field_simp
    ring
  simp only [h0, h1, h2v, h3, h4, h5, map_neg]
  ring

noncomputable def cubicEuler {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  regularEuler cubicB3 cubicB2 cubicB1 cubicB0 P

theorem cubicEuler_eq {K : Type*} [CommRing K] (P : K[X]) :
    cubicEuler P = X ^ 3 * cubicOperator P := by
  simp [cubicEuler, regularEuler, cubicB3, cubicB2, cubicB1, cubicB0,
    cubicOperator, theta, derivative_mul]
  ring

theorem theta_monomial {K : Type*} [CommRing K] (n : ℕ) (c : K) :
    theta (C c * X ^ n) = C ((n : K) * c) * X ^ n := by
  ext k
  simp only [theta_coeff, coeff_C_mul, coeff_X_pow]
  by_cases h : k = n
  · subst k
    simp
  · simp [h]

theorem cubicEuler_monomial {K : Type*} [CommRing K] (n : ℕ) (c : K) :
    cubicEuler (C c * X ^ n) = C c * X ^ n * indicialPolynomial (n : K) := by
  simp only [cubicEuler, regularEuler, theta_monomial]
  simp only [indicialPolynomial, map_mul, map_pow]
  ring

theorem cubicEuler_add {K : Type*} [CommRing K] (P Q : K[X]) :
    cubicEuler (P + Q) = cubicEuler P + cubicEuler Q := by
  simp [cubicEuler, regularEuler, theta, derivative_add]
  ring

/-- Universal finite reciprocal covariance at N=-1/2 in the coefficient field. -/
theorem actual_cubic_reciprocal_covariance {K : Type*} [Field K]
    (N : ℕ) (h2 : (2 : K) ≠ 0) (hN : 2 * (N : K) + 1 = 0)
    (P : K[X]) (hdegree : P.natDegree ≤ N) :
    cubicEuler (P.reflect N) = -(cubicEuler P).reflect (N + 5) := by
  have hhalf : (N : K) = -(1 / 2) := by
    field_simp
    linear_combination hN
  refine induction_with_natDegree_le
    (fun P => cubicEuler (P.reflect N) = -(cubicEuler P).reflect (N + 5)) N ?_ ?_ ?_ P hdegree
  · simp [cubicEuler, regularEuler, theta]
  · intro n c _ hn
    rw [reflect_C_mul_X_pow, revAt_le hn, cubicEuler_monomial, cubicEuler_monomial,
      reflect_mul _ _ (natDegree_C_mul_X_pow_le c n |>.trans hn) (indicial_degree _),
      reflect_C_mul_X_pow, revAt_le hn]
    have hind : indicialPolynomial ((N - n : ℕ) : K) = -(indicialPolynomial (n : K)).reflect 5 := by
      rw [Nat.cast_sub hn, hhalf]
      exact actual_indicial_reciprocal h2 (n : K)
    rw [hind]
    ring
  · intro A B _ _ hA hB
    rw [reflect_add, cubicEuler_add, hA, hB, cubicEuler_add, reflect_add]
    ring

theorem actual_cubic_reciprocal_solution {K : Type*} [Field K]
    (N : ℕ) (h2 : (2 : K) ≠ 0) (hN : 2 * (N : K) + 1 = 0)
    (P : K[X]) (hdegree : P.natDegree ≤ N) (hODE : cubicOperator P = 0) :
    cubicOperator (P.reflect N) = 0 := by
  have h := actual_cubic_reciprocal_covariance N h2 hN P hdegree
  rw [cubicEuler_eq, cubicEuler_eq, hODE, mul_zero, reflect_zero, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 X_ne_zero)

end WPHasseReciprocity
