import WPActualRankTwoProper
import WPActualRankTwoResidueSource

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualCMGauss WPActualGaussProper
  WPActualRankTwoGaussODE WPActualRankTwoProper

namespace WPActualRankTwoFiniteLegendre

set_option maxHeartbeats 800000

theorem legendreJacobi_theta {K : Type*} [CommRing K] (d : ℕ) (P : K[X]) :
    legendreJacobi d P = P.derivative.derivative - theta (theta P) - theta P +
      C ((d : K) * ((d : K) + 1)) * P := by
  simp [legendreJacobi, theta, derivative_mul]
  ring

theorem legendreJacobi_coeff {K : Type*} [CommRing K] (d n : ℕ) (P : K[X]) :
    (legendreJacobi d P).coeff n =
      ((n : K) + 1) * ((n : K) + 2) * P.coeff (n + 2) +
        ((d : K) * ((d : K) + 1) - (n : K) * ((n : K) + 1)) * P.coeff n := by
  rw [legendreJacobi_theta]
  simp only [coeff_add, coeff_sub, coeff_C_mul, theta_coeff, coeff_derivative,
    Nat.cast_add, Nat.cast_one]
  ring

theorem legendre_regular_kernel_zero (p d : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdegree : P.natDegree < p) (horigin : P.eval 0 = 0)
    (hsource : legendreRegular d P = 0) : P = 0 := by
  have he : legendreEuler d P = 0 := by
    rw [legendreEuler_eq_X_regular, hsource, mul_zero]
  have hz : ∀ n, n < p → P.coeff n = 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [coeff_zero_eq_eval_zero]
      exact horigin
    | succ n ih =>
      intro hn
      have hu : ((n : ZMod p) + 1) ≠ 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          small_cast_ne_zero p (n + 1) (by omega) hn
      have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (n + 1)) he
      rw [legendreEuler_coeff_succ, coeff_zero, ih (by omega), mul_zero, sub_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero 2 hu)
  ext n
  rw [coeff_zero]
  by_cases hn : n < p
  · exact hz n hn
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem jacobi_coordinate_inverse {K : Type*} [CommRing K] (a : K) (ha : 2 * a = 1) :
    (C a * (1 - X)).comp (1 - 2 * X) = (X : K[X]) ∧
      (1 - 2 * X : K[X]).comp (C a * (1 - X)) = (X : K[X]) := by
  have haP : 2 * C a = (1 : K[X]) := by
    have h := congrArg (C : K → K[X]) ha
    simpa only [map_mul, map_ofNat, map_one] using h
  constructor
  · simp [Polynomial.mul_comp, Polynomial.sub_comp]
    linear_combination X * haP
  · rw [show (2 : K[X]) = C (2 : K) by rfl]
    simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.one_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    simp only [map_ofNat]
    linear_combination -(1 - X) * haP

/-- The degree bound excludes every extra characteristic-p homogeneous slot. -/
theorem legendre_jacobi_kernel_zero (p d : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree < p) (hend : P.eval 1 = 0)
    (hsource : legendreJacobi d P = 0) : P = 0 := by
  let q : (ZMod p)[X] := C (1 / 2 : ZMod p) * (1 - X)
  let g : (ZMod p)[X] := 1 - 2 * X
  have hi := jacobi_coordinate_inverse (1 / 2 : ZMod p) (field_half_identity p hp)
  have hqg : q.comp g = X := hi.1
  have hgq : g.comp q = X := hi.2
  have hcoord := legendre_coordinate d (1 / 2 : ZMod p) (field_half_identity p hp) (P.comp g)
  change (legendreRegular d (P.comp g)).comp q = legendreJacobi d ((P.comp g).comp q) at hcoord
  rw [Polynomial.comp_assoc, hgq, Polynomial.comp_X, hsource] at hcoord
  have hreg := congrArg (fun Q : (ZMod p)[X] => Q.comp g) hcoord
  rw [Polynomial.comp_assoc, hqg, Polynomial.comp_X, Polynomial.zero_comp] at hreg
  have hc : g.natDegree ≤ 1 := by dsimp [g]; compute_degree
  have hdeg : (P.comp g).natDegree < p :=
    Polynomial.natDegree_comp_le.trans_lt ((Nat.mul_le_mul_left _ hc).trans_lt (by simpa))
  have horigin : (P.comp g).eval 0 = 0 := by simp [Polynomial.eval_comp, g, hend]
  have hz := legendre_regular_kernel_zero p d (P.comp g) hdeg horigin hreg
  have hh := congrArg (fun Q : (ZMod p)[X] => Q.comp q) hz
  simpa only [Polynomial.comp_assoc, hgq, Polynomial.comp_X, Polynomial.zero_comp] using hh

theorem forced_legendre_degree_bound (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree ≤ p + p / 6 - 1)
    (hsource : (legendreJacobi (p / 6) P).natDegree ≤ p / 6) :
    P.natDegree ≤ p - 1 - p / 6 := by
  by_cases hP : P = 0
  · simp [hP]
  by_contra hb
  let m := P.natDegree
  have hm : p - 1 - p / 6 < m := by dsimp [m]; omega
  have hmupper : m ≤ p + p / 6 - 1 := hdegree
  have hmhigh : p / 6 < m := by omega
  have hu1 := small_cast_ne_zero p (m - p / 6) (by omega) (by omega)
  have hu2 := small_cast_ne_zero p (m + p / 6 + 1 - p) (by omega) (by omega)
  have hdiff : (m : ZMod p) - ((p / 6 : ℕ) : ZMod p) = ((m - p / 6 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : p / 6 ≤ m)]
  have hsum : ((m + p / 6 + 1 - p : ℕ) : ZMod p) =
      (m : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1 := by
    rw [Nat.cast_sub (by omega : p ≤ m + p / 6 + 1)]
    simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, sub_zero]
  have hu : ((m : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
      ((m : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1) ≠ 0 := by
    rw [hdiff, ← hsum]
    exact mul_ne_zero hu1 hu2
  have ht := legendreJacobi_coeff (p / 6) m P
  rw [coeff_eq_zero_of_natDegree_lt (hsource.trans_lt hmhigh),
    coeff_eq_zero_of_natDegree_lt (by dsimp [m]; omega), mul_zero, zero_add] at ht
  have hz : ((m : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
      ((m : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1) * P.coeff m = 0 := by
    linear_combination ht
  have hcoef := (mul_eq_zero.mp hz).resolve_left hu
  exact (leadingCoeff_ne_zero.mpr hP) (by simpa only [m, coeff_natDegree] using hcoef)

end WPActualRankTwoFiniteLegendre
