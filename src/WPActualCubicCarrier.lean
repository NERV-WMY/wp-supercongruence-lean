import WPActualCubicGauge

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeFirstIntegral WPActualCubicGauge

namespace WPActualCubicCarrier

/-- Every original coefficient is retained before clearing the cubic denominator. -/
noncomputable def cubicLift {K : Type*} [CommRing K] (d N : ℕ) (P : K[X]) : K[X] :=
  ∑ n ∈ Finset.range (d + 1), C (P.coeff n) * cubicA ^ n * cubicH ^ (N - 3 * n)

theorem cubicH_power_derivative {K : Type*} [CommRing K] (n : ℕ) :
    cubicH * ((cubicH : K[X]) ^ n).derivative = 8 * C (n : K) * cubicH ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, derivative_mul, cubicH_derivative, Nat.cast_add, Nat.cast_one,
      map_add, map_one]
    linear_combination cubicH * ih

theorem cubicLift_term_zero {K : Type*} [CommRing K] (N : ℕ) (c : K) :
    cubicH ^ 4 * (C c * cubicH ^ N).derivative -
      8 * C (N : K) * cubicH ^ 3 * (C c * cubicH ^ N) = 0 := by
  simp only [derivative_mul, derivative_C, zero_mul, zero_add]
  linear_combination C c * cubicH ^ 3 * cubicH_power_derivative (K := K) N

theorem cubicLift_term_succ {K : Type*} [CommRing K] (N n : ℕ) (c : K)
    (hn : 3 * (n + 1) ≤ N) :
    cubicH ^ 4 * (C c * cubicA ^ (n + 1) * cubicH ^ (N - 3 * (n + 1))).derivative -
      8 * C (N : K) * cubicH ^ 3 * (C c * cubicA ^ (n + 1) * cubicH ^ (N - 3 * (n + 1))) =
        cubicB * C (((n + 1 : ℕ) : K) * c) * cubicA ^ n * cubicH ^ (N - 3 * n) := by
  have he : N - 3 * n = N - 3 * (n + 1) + 3 := by omega
  have hc : (N : K) = ((N - 3 * (n + 1) : ℕ) : K) + 3 * ((n : K) + 1) := by
    have hnat : N = N - 3 * (n + 1) + 3 * (n + 1) := by omega
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      congrArg (fun t : ℕ => (t : K)) hnat
  have hpow : (cubicH : K[X]) ^ (N - 3 * n) =
      cubicH ^ (N - 3 * (n + 1)) * cubicH ^ 3 := by rw [he, pow_add]
  rw [hpow, cubicB_source, hc]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_pow_succ,
    Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat, map_one]
  linear_combination C c * cubicA ^ (n + 1) * cubicH ^ 3 *
    cubicH_power_derivative (K := K) (N - 3 * (n + 1))

theorem cubicLift_derivative {K : Type*} [CommRing K] (d N : ℕ) (P : K[X])
    (hdegree : P.natDegree ≤ d) (hN : 3 * d ≤ N) :
    cubicH ^ 4 * (cubicLift d N P).derivative -
      8 * C (N : K) * cubicH ^ 3 * cubicLift d N P = cubicB * cubicLift d N P.derivative := by
  have ht : P.coeff (d + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  calc
    _ = ∑ n ∈ Finset.range (d + 1),
        (cubicH ^ 4 * (C (P.coeff n) * cubicA ^ n * cubicH ^ (N - 3 * n)).derivative -
          8 * C (N : K) * cubicH ^ 3 * (C (P.coeff n) * cubicA ^ n * cubicH ^ (N - 3 * n))) := by
      simp only [cubicLift, derivative_sum, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = ∑ n ∈ Finset.range (d + 1), cubicB * C ((n : K) * P.coeff n) *
        cubicA ^ (n - 1) * cubicH ^ (N - 3 * (n - 1)) := by
      apply Finset.sum_congr rfl
      intro n hn
      cases n with
      | zero => simpa using cubicLift_term_zero (K := K) N (P.coeff 0)
      | succ n =>
        have hnd : n + 1 ≤ d := by have := Finset.mem_range.mp hn; omega
        exact cubicLift_term_succ N n (P.coeff (n + 1)) (by omega)
    _ = ∑ n ∈ Finset.range d, cubicB * C (((n + 1 : ℕ) : K) * P.coeff (n + 1)) *
        cubicA ^ n * cubicH ^ (N - 3 * n) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_cancel, Nat.cast_zero, zero_mul, map_zero, mul_zero, add_zero]
    _ = cubicB * cubicLift d N P.derivative := by
      simp only [cubicLift, Finset.mul_sum, coeff_derivative]
      rw [Finset.sum_range_succ]
      simp only [ht, mul_zero, map_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [map_mul, Nat.cast_add, Nat.cast_one, map_add, map_one]
      ring

theorem cubicLift_origin {K : Type*} [CommRing K] (d N : ℕ) (P : K[X]) :
    (cubicLift d N P).eval 0 = P.eval 0 := by
  have ha : (cubicA : K[X]).eval 0 = 0 := by simp [cubicA]
  have hh : (cubicH : K[X]).eval 0 = 1 := by simp [cubicH]
  simp only [cubicLift, Polynomial.eval_finsetSum, eval_mul, eval_C, eval_pow,
    ha, hh, one_pow, mul_one]
  rw [Finset.sum_eq_single 0]
  · simp [coeff_zero_eq_eval_zero]
  · intro n hn hn0
    simp [zero_pow hn0]
  · simp

theorem cubicLift_degree {K : Type*} [CommRing K] (d N : ℕ) (P : K[X]) (hN : 3 * d ≤ N) :
    (cubicLift d N P).natDegree ≤ N + d := by
  have hA : (cubicA : K[X]).natDegree ≤ 4 := by unfold cubicA; compute_degree
  have hH : (cubicH : K[X]).natDegree ≤ 1 := by unfold cubicH; compute_degree
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [cubicLift, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro n hn
  have hnd : n ≤ d := by have := Finset.mem_range.mp hn; omega
  have hAp := power_degree_bound (cubicA : K[X]) 4 n hA
  have hHp := power_degree_bound (cubicH : K[X]) 1 (N - 3 * n) hH
  have hc : (C (P.coeff n)).natDegree ≤ 0 := by simp
  have ht := natDegree_mul_le_of_le (natDegree_mul_le_of_le hc hAp) hHp
  exact coeff_eq_zero_of_natDegree_lt (ht.trans_lt (by omega))

noncomputable def actualNativeCarrier (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  cubicLift (p / 6) ((p - 1) / 2) (nativeField p (p / 6))

theorem actualNativeCarrier_origin (p : ℕ) [Fact p.Prime] :
    (actualNativeCarrier p).eval 0 = 1 := by
  rw [actualNativeCarrier, cubicLift_origin, actual_native_field_origin]

theorem actualNativeCarrier_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualNativeCarrier p).natDegree < p := by
  have he := WPActualNativeParameter.prime_six_classes p hp
  have hN : 3 * (p / 6) ≤ (p - 1) / 2 := by rcases he with he | he <;> omega
  have hd := cubicLift_degree (p / 6) ((p - 1) / 2) (nativeField p (p / 6)) hN
  change (actualNativeCarrier p).natDegree ≤ (p - 1) / 2 + p / 6 at hd
  exact hd.trans_lt (by omega)

theorem actual_half_gauge (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    8 * (((p - 1) / 2 : ℕ) : ZMod p) + 4 = 0 := by
  have hn := WPActualHasseReciprocal.actual_half_exponent p hp
  have hf : 2 * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
    have he := congrArg (fun n : ℕ => (n : ZMod p)) hn
    simpa using he
  linear_combination 4 * hf

theorem cubicLift_actual_gauge (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (P : (ZMod p)[X]) (hdegree : P.natDegree ≤ p / 6) :
    cubicH ^ 4 * (cubicLift (p / 6) ((p - 1) / 2) P).derivative +
      4 * cubicH ^ 3 * cubicLift (p / 6) ((p - 1) / 2) P =
        cubicB * cubicLift (p / 6) ((p - 1) / 2) P.derivative := by
  have hN : 3 * (p / 6) ≤ (p - 1) / 2 := by
    rcases WPActualNativeParameter.prime_six_classes p hp with he | he <;> omega
  have he := cubicLift_derivative (p / 6) ((p - 1) / 2) P hdegree hN
  have hc : 8 * C ((((p - 1) / 2 : ℕ) : ZMod p)) + 4 = 0 := by
    have hh := congrArg (Polynomial.C (R := ZMod p)) (actual_half_gauge p hp)
    simpa only [map_add, map_mul, C_ofNat, map_zero] using hh
  linear_combination he + cubicH ^ 3 * cubicLift (p / 6) ((p - 1) / 2) P * hc

end WPActualCubicCarrier
