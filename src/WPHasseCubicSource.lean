import WPActualNativeHasse
import WPActualPullbackSource

open scoped BigOperators Polynomial
open Polynomial WPActualNativeHasse WPActualPullbackSource

namespace WPHasseCubicSource

/-- The denominator-cleared ordinary native operator; X times this is the Euler operator. -/
noncomputable def regularNative {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  72 * X ^ 2 * (1 - X) * derivative (derivative (derivative P)) +
  (216 * X - 324 * X ^ 2) * derivative (derivative P) +
  (72 - 226 * X) * derivative P - 5 * P

theorem clearedOperator_eq_X_regular {K : Type*} [CommRing K] (P : K[X]) :
    clearedOperator P = X * regularNative P := by
  simp [clearedOperator, regularNative, integerShift, theta, derivative_mul, map_ofNat]
  ring

theorem actual_native_field_regular_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    regularNative (nativeField p (p / 6)) = 0 := by
  apply mul_left_cancel₀ (show (X : (ZMod p)[X]) ≠ 0 from X_ne_zero)
  rw [mul_zero, ← clearedOperator_eq_X_regular, actual_native_field_ODE p hp]

noncomputable def cubicDiscriminant {K : Type*} [CommRing K] : K[X] :=
  (4 - X) * (4 * X - 1)
noncomputable def cubicNumerator {K : Type*} [CommRing K] : K[X] :=
  (4 * X - 1) ^ 2 * (4 - X)

noncomputable def cubicA3 {K : Type*} [CommRing K] : K[X] :=
  8 * (X + 1) * cubicDiscriminant ^ 2
noncomputable def cubicA2 {K : Type*} [CommRing K] : K[X] :=
  12 * cubicDiscriminant ^ 2 + 24 * (X + 1) * cubicDiscriminant * derivative cubicDiscriminant
noncomputable def cubicA1 {K : Type*} [CommRing K] : K[X] :=
  16 * cubicDiscriminant * derivative cubicDiscriminant +
  8 * (X + 1) * (cubicDiscriminant * derivative (derivative cubicDiscriminant) +
    derivative cubicDiscriminant ^ 2) - 10 * cubicNumerator
noncomputable def cubicA0 {K : Type*} [CommRing K] : K[X] := -5 * derivative cubicNumerator

/-- The same finite cubic operator in the actual x=5t^2-1 coordinate. -/
noncomputable def cubicOperator {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  cubicA3 * derivative (derivative (derivative P)) + cubicA2 * derivative (derivative P) +
    cubicA1 * derivative P + cubicA0 * P

/-- Universal actual cubic source transport; no homogeneous source is imposed on P. -/
theorem actual_cubic_pullback_source (P : ℚ[X]) :
    cubicOperator (P.comp Vpolynomial) =
      3 * (4 * X - 1) * (11 - 4 * X) * (regularNative P).comp Vpolynomial := by
  apply Polynomial.funext
  intro x
  simp [cubicOperator, cubicA3, cubicA2, cubicA1, cubicA0, cubicDiscriminant,
    cubicNumerator, regularNative, Vpolynomial, derivative_comp, derivative_mul,
    derivative_pow_succ]
  ring

/-- A lower-coefficient hypothesis turns an Euler product into its exact indicial term. -/
theorem coeff_mul_under_vanishing {K : Type*} [CommRing K] (A P : K[X]) (n : ℕ)
    (hP : ∀ k < n, P.coeff k = 0) : (A * P).coeff n = A.coeff 0 * P.coeff n := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_single (0, n)
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    have hk : ij.2 < n := by
      have hi : ij.1 ≠ 0 := by
        intro hi
        apply hne
        ext <;> omega
      omega
    rw [hP ij.2 hk, mul_zero]
  · intro h
    exact False.elim (h (by simp))

noncomputable def regularEuler {K : Type*} [CommRing K]
    (E3 E2 E1 E0 P : K[X]) : K[X] :=
  E3 * theta (theta (theta P)) + E2 * theta (theta P) + E1 * theta P + E0 * P

theorem regularEuler_indicial {K : Type*} [CommRing K]
    (E3 E2 E1 E0 P : K[X]) (n : ℕ) (hP : ∀ k < n, P.coeff k = 0) :
    (regularEuler E3 E2 E1 E0 P).coeff n =
      (E3.coeff 0 * (n : K) ^ 3 + E2.coeff 0 * (n : K) ^ 2 +
        E1.coeff 0 * (n : K) + E0.coeff 0) * P.coeff n := by
  have h1 : ∀ k < n, (theta P).coeff k = 0 := by
    intro k hk; rw [theta_coeff, hP k hk, mul_zero]
  have h2 : ∀ k < n, (theta (theta P)).coeff k = 0 := by
    intro k hk; rw [theta_coeff, h1 k hk, mul_zero]
  have h3 : ∀ k < n, (theta (theta (theta P))).coeff k = 0 := by
    intro k hk; rw [theta_coeff, h2 k hk, mul_zero]
  simp only [regularEuler, coeff_add, coeff_mul_under_vanishing _ _ n hP,
    coeff_mul_under_vanishing _ _ n h1, coeff_mul_under_vanishing _ _ n h2,
    coeff_mul_under_vanishing _ _ n h3, theta_coeff]
  ring

/-- Finite endpoint uniqueness, with the degree<p hypothesis explicitly load-bearing. -/
theorem finite_regularEuler_uniqueness (p : ℕ) [Fact p.Prime]
    (E3 E2 E1 E0 P : (ZMod p)[X]) (c : ZMod p) (hc : c ≠ 0)
    (hE3 : E3.coeff 0 = c) (hE2 : E2.coeff 0 = 0)
    (hE1 : E1.coeff 0 = 0) (hE0 : E0.coeff 0 = 0)
    (hdegree : P.natDegree < p) (horigin : P.eval 0 = 0)
    (hODE : regularEuler E3 E2 E1 E0 P = 0) : P = 0 := by
  ext n
  rw [coeff_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact (coeff_zero_eq_eval_zero P).trans horigin
    · by_cases hnp : n < p
      · have hnc : (n : ZMod p) ≠ 0 := by
          rw [ne_eq, ZMod.natCast_eq_zero_iff]
          intro hd
          have hle := Nat.le_of_dvd (by omega : 0 < n) hd
          omega
        have hi := regularEuler_indicial E3 E2 E1 E0 P n ih
        rw [hODE, coeff_zero, hE3, hE2, hE1, hE0] at hi
        have hprod : c * (n : ZMod p) ^ 3 * P.coeff n = 0 := by simpa using hi.symm
        exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hc (pow_ne_zero 3 hnc))
      · exact coeff_eq_zero_of_natDegree_lt (by omega)

end WPHasseCubicSource
