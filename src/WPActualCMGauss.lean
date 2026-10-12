import WPActualNativeFirstIntegral
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeParameter

namespace WPActualCMGauss

/-- The full integer Legendre coefficient recurrence, including its terminal coefficient. -/
theorem shiftedLegendre_cleared_recurrence (k n : ℕ) :
    ((n : ℤ) + 1) ^ 2 * (shiftedLegendre k).coeff (n + 1) =
      ((n : ℤ) - k) * ((n : ℤ) + k + 1) * (shiftedLegendre k).coeff n := by
  rw [coeff_shiftedLegendre, coeff_shiftedLegendre]
  by_cases hn : n ≤ k
  · have h1 : (k.choose (n + 1) : ℤ) * ((n : ℤ) + 1) =
        (k.choose n : ℤ) * ((k : ℤ) - n) := by
      have h := Nat.choose_succ_right_eq k n
      exact_mod_cast h
    have hsub : k + n + 1 - k = n + 1 := by omega
    have h2 : ((k + n).choose k : ℤ) * ((k : ℤ) + n + 1) =
        ((k + n + 1).choose k : ℤ) * ((n : ℤ) + 1) := by
      have h := Nat.choose_mul_succ_eq (k + n) k
      rw [hsub] at h
      exact_mod_cast h
    rw [pow_succ]
    calc
      _ = -(-1 : ℤ) ^ n * ((k.choose (n + 1) : ℤ) * ((n : ℤ) + 1)) *
          (((k + n + 1).choose k : ℤ) * ((n : ℤ) + 1)) := by
        rw [show k + (n + 1) = k + n + 1 by omega]
        ring
      _ = _ := by rw [h1, ← h2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : k < n + 1),
      Nat.choose_eq_zero_of_lt (by omega : k < n)]
    simp

noncomputable def legendreEuler {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) : K[X] :=
  theta (theta P) - X * (theta (theta P) + theta P - C ((k : K) * (k + 1)) * P)

noncomputable def legendreRegular {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) : K[X] :=
  (X - X ^ 2) * P.derivative.derivative + (1 - 2 * X) * P.derivative +
    C ((k : K) * (k + 1)) * P

theorem legendreEuler_coeff_zero {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) :
    (legendreEuler k P).coeff 0 = 0 := by
  simp [legendreEuler, theta_coeff]

theorem legendreEuler_coeff_succ {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) (n : ℕ) :
    (legendreEuler k P).coeff (n + 1) =
      ((n : K) + 1) ^ 2 * P.coeff (n + 1) -
      ((n : K) - k) * ((n : K) + k + 1) * P.coeff n := by
  simp only [legendreEuler, coeff_sub, coeff_X_mul, coeff_add, coeff_C_mul,
    theta_coeff, Nat.cast_add, Nat.cast_one]
  ring

theorem legendreEuler_eq_X_regular {K : Type*} [CommRing K] (k : ℕ) (P : K[X]) :
    legendreEuler k P = X * legendreRegular k P := by
  simp only [legendreEuler, legendreRegular, theta, derivative_mul, derivative_X, one_mul]
  ring

theorem actual_integer_legendre_ODE (k : ℕ) : legendreRegular k (shiftedLegendre k) = 0 := by
  have he : legendreEuler k (shiftedLegendre k) = 0 := by
    ext n
    cases n with
    | zero => rw [legendreEuler_coeff_zero, coeff_zero]
    | succ n =>
      rw [legendreEuler_coeff_succ, coeff_zero]
      exact sub_eq_zero.mpr (shiftedLegendre_cleared_recurrence k n)
  rw [legendreEuler_eq_X_regular] at he
  exact (mul_eq_zero.mp he).resolve_left X_ne_zero

theorem legendreRegular_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (k : ℕ) (P : K[X]) :
    (legendreRegular k P).map f = legendreRegular k (P.map f) := by
  simp [legendreRegular, derivative_map]

/-- The actual finite Gauss polynomial in the cubic variable z. -/
noncomputable def actualGauss (p : ℕ) : (ZMod p)[X] :=
  (shiftedLegendre (p / 3)).map (Int.castRingHom (ZMod p))

theorem actualGauss_coeff (p n : ℕ) : (actualGauss p).coeff n =
    ((-1 : ℤ) ^ n * (p / 3).choose n * (p / 3 + n).choose (p / 3) : ℤ) := by
  rw [actualGauss, coeff_map, coeff_shiftedLegendre]
  rfl

theorem actualGauss_origin (p : ℕ) : (actualGauss p).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, actualGauss_coeff]
  simp

theorem actualGauss_degree (p : ℕ) : (actualGauss p).natDegree ≤ p / 3 := by
  exact natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])

theorem actualGauss_reflection (p : ℕ) :
    (-1 : (ZMod p)[X]) ^ (p / 3) * (actualGauss p).comp (1 - X) = actualGauss p := by
  have h := congrArg (fun P : ℤ[X] => P.map (Int.castRingHom (ZMod p)))
    (neg_one_pow_mul_shiftedLegendre_comp_one_sub_X_eq (p / 3))
  simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg, Polynomial.map_one,
    Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_X, actualGauss] using h

theorem actualGauss_endpoint (p : ℕ) : (actualGauss p).eval 1 = (-1 : ZMod p) ^ (p / 3) := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) (actualGauss_reflection p)
  simpa [actualGauss_origin] using h.symm

theorem prime_gauss_classes (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    3 * (p / 3) + 1 = p ∨ 3 * (p / 3) + 2 = p := by
  rcases prime_six_classes p hp with h1 | h5 <;> omega

theorem actualGauss_eigenvalue (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    9 * ((p / 3 : ℕ) : ZMod p) * (((p / 3 : ℕ) : ZMod p) + 1) = (-2 : ZMod p) := by
  have hpfield : (3 * ((p / 3 : ℕ) : ZMod p) + 1) *
      (3 * ((p / 3 : ℕ) : ZMod p) + 2) = 0 := by
    rcases prime_gauss_classes p hp with h1 | h2
    · have h : 3 * ((p / 3 : ℕ) : ZMod p) + 1 = 0 := by
        have hc : 3 * ((p / 3 : ℕ) : ZMod p) + 1 = (p : ZMod p) := by
          simpa using congrArg (fun n : ℕ => (n : ZMod p)) h1
        rw [hc, ZMod.natCast_self]
      rw [h, zero_mul]
    · have h : 3 * ((p / 3 : ℕ) : ZMod p) + 2 = 0 := by
        have hc : 3 * ((p / 3 : ℕ) : ZMod p) + 2 = (p : ZMod p) := by
          simpa using congrArg (fun n : ℕ => (n : ZMod p)) h2
        rw [hc, ZMod.natCast_self]
      rw [h, mul_zero]
  linear_combination hpfield

theorem actualGauss_cleared_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    9 * (X - X ^ 2) * (actualGauss p).derivative.derivative +
      9 * (1 - 2 * X) * (actualGauss p).derivative - 2 * actualGauss p = 0 := by
  have he : legendreRegular (p / 3) (actualGauss p) = 0 := by
    rw [actualGauss, ← legendreRegular_map, actual_integer_legendre_ODE, Polynomial.map_zero]
  have hc : (9 : (ZMod p)[X]) * C (((p / 3 : ℕ) : ZMod p) * (((p / 3 : ℕ) : ZMod p) + 1)) = -2 := by
    have hv := actualGauss_eigenvalue p hp
    simpa only [map_mul, map_ofNat, map_neg, Nat.cast_add, Nat.cast_one, mul_assoc] using
      congrArg Polynomial.C hv
  calc
    _ = 9 * legendreRegular (p / 3) (actualGauss p) -
        (9 * C (((p / 3 : ℕ) : ZMod p) * (((p / 3 : ℕ) : ZMod p) + 1)) + 2) * actualGauss p := by
      unfold legendreRegular
      ring
    _ = 0 := by rw [he, hc]; ring

end WPActualCMGauss
