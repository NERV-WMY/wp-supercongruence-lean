import WPActualCMGauss

open scoped Polynomial
open Polynomial WPActualNativeHasse WPHasseCubicSource WPActualCMGauss

namespace WPActualCMGaussSquare

noncomputable def gaussRegular {K : Type*} [CommRing K] (Y : K[X]) : K[X] :=
  9 * X * (1 - X) * Y.derivative.derivative +
    9 * (1 - 2 * X) * Y.derivative - 2 * Y

noncomputable def squareRegular {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  9 * X ^ 2 * (1 - X) ^ 2 * P.derivative.derivative.derivative +
    27 * X * (1 - X) * (1 - 2 * X) * P.derivative.derivative +
    (9 - 62 * X + 62 * X ^ 2) * P.derivative - 4 * (1 - 2 * X) * P

/-- The full symmetric-square source, before imposing the actual Gauss ODE. -/
theorem squareRegular_source {K : Type*} [CommRing K] (Y : K[X]) :
    squareRegular (Y ^ 2) =
      2 * X * (1 - X) * Y * (gaussRegular Y).derivative +
        (6 * X * (1 - X) * Y.derivative + 2 * (1 - 2 * X) * Y) * gaussRegular Y := by
  simp [squareRegular, gaussRegular, derivative_mul, derivative_pow_succ]
  ring

theorem actualGauss_square_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    squareRegular (actualGauss p ^ 2) = 0 := by
  have he : gaussRegular (actualGauss p) = 0 := by
    convert actualGauss_cleared_ODE p hp using 1
    unfold gaussRegular
    ring
  rw [squareRegular_source, he, derivative_zero]
  ring

noncomputable def squareE3 {K : Type*} [CommRing K] : K[X] := 9 * (1 - X) ^ 2
noncomputable def squareE2 {K : Type*} [CommRing K] : K[X] := -27 * X * (1 - X)
noncomputable def squareE1 {K : Type*} [CommRing K] : K[X] := -17 * X + 26 * X ^ 2
noncomputable def squareE0 {K : Type*} [CommRing K] : K[X] := -4 * X + 8 * X ^ 2

theorem squareRegular_euler {K : Type*} [CommRing K] (P : K[X]) :
    regularEuler squareE3 squareE2 squareE1 squareE0 P = X * squareRegular P := by
  simp [regularEuler, squareE3, squareE2, squareE1, squareE0, squareRegular,
    theta, derivative_mul]
  ring

theorem squareRegular_sub {K : Type*} [CommRing K] (P Q : K[X]) :
    squareRegular (P - Q) = squareRegular P - squareRegular Q := by
  simp only [squareRegular, derivative_sub]
  ring

theorem actualGauss_square_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualGauss p ^ 2).natDegree < p := by
  have he : (actualGauss p ^ 2).natDegree ≤ p / 3 + p / 3 := by
    simpa only [pow_two] using natDegree_mul_le_of_le (actualGauss_degree p)
      (actualGauss_degree p)
  rcases prime_gauss_classes p hp with h1 | h2 <;> omega

/-- The original degree bound excludes every Frobenius ambiguity in the cubic carrier. -/
theorem actualGauss_square_unique (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p) (horigin : P.eval 0 = 1)
    (hsource : squareRegular P = 0) : P = actualGauss p ^ 2 := by
  have hu : (3 : ZMod p) ≠ 0 := by
    change ((3 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hd
    have hle := Nat.le_of_dvd (by omega : 0 < 3) hd
    omega
  have h9 : (9 : ZMod p) ≠ 0 := by
    have hsq : (9 : ZMod p) = 3 ^ 2 := by norm_num
    rw [hsq]
    exact pow_ne_zero 2 hu
  have hcoeff : (squareE3 : (ZMod p)[X]).coeff 0 = 9 ∧
      (squareE2 : (ZMod p)[X]).coeff 0 = 0 ∧
      (squareE1 : (ZMod p)[X]).coeff 0 = 0 ∧
      (squareE0 : (ZMod p)[X]).coeff 0 = 0 := by
    simp [squareE3, squareE2, squareE1, squareE0, coeff_zero_eq_eval_zero]
  have hdeg : (P - actualGauss p ^ 2).natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hdegree (actualGauss_square_degree p hp))
  have hzero := finite_regularEuler_uniqueness p squareE3 squareE2 squareE1 squareE0
    (P - actualGauss p ^ 2) 9 h9 hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2 hdeg
    (by simp [horigin, actualGauss_origin]) (by
      rw [squareRegular_euler, squareRegular_sub, hsource, actualGauss_square_ODE p hp]
      ring)
  exact sub_eq_zero.mp hzero

end WPActualCMGaussSquare
