import WPActualCubicCarrier
import Mathlib.FieldTheory.RatFunc.AsPolynomial

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeFirstIntegral WPHasseCubicSource
  WPActualCMGauss WPActualCMGaussSquare WPActualCubicGauge WPActualCubicCarrier

namespace WPActualCubicHasse

theorem cubicH_ne_zero {K : Type*} [CommRing K] [Nontrivial K] : (cubicH : K[X]) ≠ 0 := by
  intro he
  have hc := congrArg (fun P : K[X] => P.eval 0) he
  simp [cubicH] at hc

theorem homogeneous_fraction_term {K : Type*} [Field K] (A H : K) (hH : H ≠ 0)
    (n N : ℕ) (hn : 3 * n ≤ N) :
    A ^ n * H ^ (N - 3 * n) = H ^ N * (A / H ^ 3) ^ n := by
  have he : H ^ N = H ^ (N - 3 * n) * H ^ (3 * n) := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [he, div_pow, ← pow_mul]
  field_simp [hH]

/-- Faithful rational evaluation of the entire coefficient-defined cubic lift. -/
theorem cubicLift_rational_eval {K : Type*} [Field K] (d N : ℕ) (P : K[X])
    (hdegree : P.natDegree ≤ d) (hN : 3 * d ≤ N) :
    algebraMap K[X] (RatFunc K) (cubicLift d N P) =
      (algebraMap K[X] (RatFunc K) cubicH) ^ N *
        P.eval₂ RatFunc.C (algebraMap K[X] (RatFunc K) cubicA /
          (algebraMap K[X] (RatFunc K) cubicH) ^ 3) := by
  have hH := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := K))
  rw [cubicLift, map_sum, eval₂_eq_sum_range' RatFunc.C
    (by omega : P.natDegree < d + 1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnd : n ≤ d := by have := Finset.mem_range.mp hn; omega
  simp only [map_mul, map_pow, RatFunc.algebraMap_C]
  have he := homogeneous_fraction_term
    (algebraMap K[X] (RatFunc K) cubicA) (algebraMap K[X] (RatFunc K) cubicH)
    hH n N (by omega)
  linear_combination RatFunc.C (P.coeff n) * he

/-- The cleared native source is obtained from the actual homogeneous polynomial, not imposed. -/
theorem cubicLift_native_source {K : Type*} [Field K] (d N : ℕ) (P : K[X])
    (hdegree : P.natDegree ≤ d) (hN : 3 * d ≤ N) (hsource : regularNative P = 0) :
    nativeGaugeSource (cubicLift d N P) (cubicLift d N P.derivative)
      (cubicLift d N P.derivative.derivative)
      (cubicLift d N P.derivative.derivative.derivative) = 0 := by
  let E := algebraMap K[X] (RatFunc K)
  let H := E cubicH
  let A := E cubicA
  let q := A / H ^ 3
  have hH : H ≠ 0 := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := K))
  have hd1 := derivative_degree_bound P d hdegree
  have hd2 := derivative_degree_bound P.derivative d hd1
  have hd3 := derivative_degree_bound P.derivative.derivative d hd2
  have he : E (nativeGaugeSource (cubicLift d N P) (cubicLift d N P.derivative)
        (cubicLift d N P.derivative.derivative)
        (cubicLift d N P.derivative.derivative.derivative)) =
      H ^ (N + 9) * (regularNative P).eval₂ RatFunc.C q := by
    simp only [E, nativeGaugeSource, map_add, map_sub, map_mul, map_pow, map_ofNat]
    rw [cubicLift_rational_eval d N P hdegree hN,
      cubicLift_rational_eval d N P.derivative hd1 hN,
      cubicLift_rational_eval d N P.derivative.derivative hd2 hN,
      cubicLift_rational_eval d N P.derivative.derivative.derivative hd3 hN]
    change 72 * A ^ 2 * (H ^ 3 - A) * (H ^ N * P.derivative.derivative.derivative.eval₂ RatFunc.C q) +
        (216 * A * H ^ 6 - 324 * A ^ 2 * H ^ 3) * (H ^ N * P.derivative.derivative.eval₂ RatFunc.C q) +
        (72 * H ^ 9 - 226 * A * H ^ 6) * (H ^ N * P.derivative.eval₂ RatFunc.C q) -
        5 * H ^ 9 * (H ^ N * P.eval₂ RatFunc.C q) = _
    simp only [regularNative, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_ofNat, eval₂_X,
      eval₂_one]
    rw [show H ^ (N + 9) = H ^ N * H ^ 9 by rw [pow_add]]
    dsimp only [q]
    field_simp [hH]
  apply RatFunc.algebraMap_injective K
  change E _ = E 0
  rw [he, hsource, eval₂_zero, mul_zero, map_zero]

/-- The actual finite native cubic carrier satisfies the full Gauss-square equation. -/
theorem actualNativeCarrier_square_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    squareRegular (actualNativeCarrier p) = 0 := by
  let d := p / 6
  let N := (p - 1) / 2
  let F := nativeField p d
  have hd0 : F.natDegree ≤ d := actual_native_field_degree p
  have hd1 := derivative_degree_bound F d hd0
  have hd2 := derivative_degree_bound F.derivative d hd1
  have hN : 3 * d ≤ N := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with he | he <;> dsimp [d, N] <;> omega
  have hs := cubicLift_native_source d N F hd0 hN (actual_native_field_regular_ODE p (by omega))
  have he := cubicGauge_source (cubicLift d N F) (cubicLift d N F.derivative)
    (cubicLift d N F.derivative.derivative) (cubicLift d N F.derivative.derivative.derivative)
    (cubicLift_actual_gauge p (by omega) F hd0)
    (cubicLift_actual_gauge p (by omega) F.derivative hd1)
    (cubicLift_actual_gauge p (by omega) F.derivative.derivative hd2)
  rw [hs, mul_zero] at he
  have h8 : (8 : ZMod p) ≠ 0 := by
    change ((8 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega : 0 < 8) hd
    omega
  have h8P : (8 : (ZMod p)[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : (ZMod p)[X] => P.coeff 0) h
    exact h8 (by simpa using hc)
  have hh := cubicH_ne_zero (K := ZMod p)
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero h8P (pow_ne_zero 12 hh))

/-- Exact original cubic Hasse identity, retaining every coefficient and both prime classes. -/
theorem actual_cubic_hasse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualNativeCarrier p = actualGauss p ^ 2 := by
  exact actualGauss_square_unique p (by omega) (actualNativeCarrier p)
    (actualNativeCarrier_degree p (by omega)) (actualNativeCarrier_origin p)
    (actualNativeCarrier_square_ODE p hp)

theorem actual_cubic_rational_hasse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ ((p - 1) / 2) *
      (nativeField p (p / 6)).eval₂ RatFunc.C
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) =
        algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (actualGauss p ^ 2) := by
  have hN : 3 * (p / 6) ≤ (p - 1) / 2 := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with he | he <;> omega
  rw [← cubicLift_rational_eval (p / 6) ((p - 1) / 2)
    (nativeField p (p / 6)) (actual_native_field_degree p) hN]
  exact congrArg (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) (actual_cubic_hasse p hp)

theorem cubicLift_point_eval {K : Type*} [Field K] (d N : ℕ) (P : K[X]) (z : K)
    (hdegree : P.natDegree ≤ d) (hN : 3 * d ≤ N) (hH : (cubicH : K[X]).eval z ≠ 0) :
    (cubicLift d N P).eval z =
      (cubicH.eval z) ^ N * P.eval (cubicA.eval z / (cubicH.eval z) ^ 3) := by
  change (cubicLift d N P).eval z = (cubicH.eval z) ^ N *
    P.eval₂ (RingHom.id K) (cubicA.eval z / (cubicH.eval z) ^ 3)
  rw [cubicLift, eval_finsetSum, eval₂_eq_sum_range' (RingHom.id K)
    (by omega : P.natDegree < d + 1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnd : n ≤ d := by have := Finset.mem_range.mp hn; omega
  simp only [eval_mul, eval_C, eval_pow, RingHom.id_apply]
  have he := homogeneous_fraction_term (cubicA.eval z) (cubicH.eval z) hH n N (by omega)
  linear_combination P.coeff n * he

/-- The original CM input is the exact center of the actual cubic carrier. -/
theorem actual_cubic_CM_hasse (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (5 : ZMod p) ^ ((p - 1) / 2) * (nativeField p (p / 6)).eval (4 / 125) =
      ((actualGauss p).eval (1 / 2)) ^ 2 := by
  have hu (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hn hd
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by exact hu 2 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := by exact hu 5 (by omega) (by omega)
  have ha : (cubicA : (ZMod p)[X]).eval (1 / 2) = 4 := by
    simp [cubicA]
    field_simp
    ring
  have hh : (cubicH : (ZMod p)[X]).eval (1 / 2) = 5 := by
    simp [cubicH]
    field_simp
    ring
  have hN : 3 * (p / 6) ≤ (p - 1) / 2 := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with he | he <;> omega
  have he := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2)) (actual_cubic_hasse p hp)
  rw [actualNativeCarrier, cubicLift_point_eval (p / 6) ((p - 1) / 2)
    (nativeField p (p / 6)) (1 / 2) (actual_native_field_degree p) hN (by rw [hh]; exact h5),
    eval_pow, ha, hh] at he
  simpa only [show (5 : ZMod p) ^ 3 = 125 by ring] using he

end WPActualCubicHasse
