import WPFieldAssembly.NativeJointSuccessorOddCollection
import WPFieldAssembly.NativeClosureMixedJ

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorOddOrigin

open NativeClosureMixedSource NativeClosureMixedJ NativeJointSuccessorOddCollection
open ActualRationalSignRows

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- The whole reflected reciprocal cubic is polynomial before its origin is selected. -/
noncomputable def oddInfinityCubic : K[X] :=
  Polynomial.C (1 / 25 : K) * WPFiniteWSource.squaredCoordinate * (4 * X - 11) ^ 2

private theorem inverse_odd_cubic_source :
    invert (oddReciprocalW : K[T;T⁻¹]) = (oddInfinityCubic : K[X]).toLaurent := by
  let x : K[T;T⁻¹] := T 1
  let t : K[T;T⁻¹] := T (-1)
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  have ht : x * t = 1 := by dsimp only [x, t]; rw [← T_add]; norm_num
  have h3 : (T 3 : K[T;T⁻¹]) = x ^ 3 := by dsimp only [x]; rw [T_pow]; norm_num
  have hc : ((5 : K) ^ 2)⁻¹ = 1 / 25 := by norm_num [one_div]
  have hz : x * (4 - 11 * t) = 4 * x - 11 := by
    linear_combination (norm := ring_nf) -11 * ht
  simp only [oddReciprocalW, map_mul, map_pow, invert_C,
    WPFiniteZSource.invert_squaredCoordinate, invert_T, neg_neg, map_sub, map_ofNat, hc,
    oddInfinityCubic, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  rw [h3]
  change LaurentPolynomial.C (1 / 25 : K) * (t * s) * x ^ 3 * (4 - 11 * t) ^ 2 =
    LaurentPolynomial.C (1 / 25 : K) * s * (4 * x - 11) ^ 2
  rw [← hz, mul_pow]
  linear_combination (norm := ring_nf)
    LaurentPolynomial.C (1 / 25 : K) * s * x ^ 2 * (4 - 11 * t) ^ 2 * ht

private theorem inverse_odd_F_source (p : ℕ) :
    invert ((oddReciprocalF p : K[X]).eval₂ LaurentPolynomial.C oddReciprocalW) =
      ((oddReciprocalF p).comp (oddInfinityCubic : K[X])).toLaurent := by
  classical
  simp only [oddReciprocalF, Polynomial.comp, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    map_sum, map_mul, map_pow, invert_C, inverse_odd_cubic_source, Polynomial.toLaurent_C]

/-- The full infinity polynomial is the original odd quotient at its reflected cubic argument. -/
theorem oddInfinityPolynomial_cubic_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (oddInfinityPolynomial p : K[X]) =
      (4 * X - 11) * (oddReciprocalF p).comp oddInfinityCubic := by
  apply Polynomial.toLaurent_injective
  have ht : (T (((p - 1) / 2 : ℕ) : ℤ) *
      T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) : K[T;T⁻¹]) = T 1 := by
    rw [← T_add]
    congr 1
    omega
  have hz : (T 1 * invert (4 - 11 * T 1) : K[T;T⁻¹]) =
      (4 * X - 11 : K[X]).toLaurent := by
    simp only [map_sub, map_mul, map_ofNat, invert_T, Polynomial.toLaurent_X]
    have hh : (T 1 * T (-1) : K[T;T⁻¹]) = 1 := by rw [← T_add]; norm_num
    linear_combination (norm := ring_nf) -11 * hh
  have hk : invert (oddReciprocalKernel p : K[T;T⁻¹]) =
      invert (4 - 11 * T 1) *
        ((oddReciprocalF p).comp (oddInfinityCubic : K[X])).toLaurent := by
    rw [oddReciprocalKernel_substitution, map_mul, inverse_odd_F_source]
  rw [oddInfinityPolynomial_source p hp, oddReciprocalS, map_mul, invert_T,
    ← mul_assoc, ht, hk, ← mul_assoc, hz, ← map_mul]

/-- Selecting the actual leading Os coefficient retains its complete finite odd cutoff. -/
theorem oddReciprocalS_origin_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (oddReciprocalS p : K[T;T⁻¹]).coeff (((p - 1) / 2 : ℕ) : ℤ) =
      -11 * (oddReciprocalF p : K[X]).eval (121 / 125) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have hw0 : (oddInfinityCubic : K[X]).eval 0 = (121 / 125 : K) := by
    simp only [oddInfinityCubic, WPFiniteWSource.squaredCoordinate, eval_mul,
      eval_C, eval_add, eval_X, eval_one, eval_sub, eval_ofNat, eval_pow, one_div,
      zero_add, mul_zero, zero_sub]
    field_simp [h5, h25, h125]
    ring
  rw [← oddInfinityPolynomial_origin p, oddInfinityPolynomial_cubic_source p hp,
    coeff_zero_eq_eval_zero, eval_mul, eval_comp, hw0]
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X, mul_zero, zero_sub]

private theorem sum_full_odd_ranges {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.Ico 1 (2 * n + 1), f j) =
      (∑ j ∈ Finset.Ico 1 (n + 1), f (2 * j)) +
        ∑ i ∈ Finset.range n, f (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega]
      rw [Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1 + 1) (by omega),
        Finset.sum_Ico_succ_top (a := 1) (b := 2 * n + 1) (by omega), ih,
        Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega),
        Finset.sum_range_succ]
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      ac_rfl

private theorem original_odd_F_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    WPFiniteField.O p z = z * (oddReciprocalF p : K[X]).eval (z ^ 2) := by
  let N := (p - 1) / 2
  have hpN : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hd : WPFiniteField.ell p z - WPFiniteField.ell p (-z) =
      2 * z * (oddReciprocalF p : K[X]).eval (z ^ 2) := by
    unfold WPFiniteField.ell
    have hsplit := sum_full_odd_ranges
      (fun j => z ^ j / (j : K) - (-z) ^ j / (j : K)) N
    rw [← hpN] at hsplit
    rw [← Finset.sum_sub_distrib, hsplit]
    have heven : (∑ j ∈ Finset.Ico 1 (N + 1),
        (z ^ (2 * j) / ((2 * j : ℕ) : K) -
          (-z) ^ (2 * j) / ((2 * j : ℕ) : K))) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hn : (-z) ^ (2 * j) = z ^ (2 * j) := by
        rw [pow_mul, neg_sq, ← pow_mul]
      rw [hn, sub_self]
    rw [heven, zero_add]
    simp only [oddReciprocalF, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hn : (-z) ^ (2 * i + 1) = -(z ^ (2 * i + 1)) := by
      simp only [pow_add, pow_mul, neg_sq, pow_one]
      ring
    rw [hn, pow_add, pow_mul, pow_one]
    ring
  unfold WPFiniteField.O
  linear_combination (norm := (field_simp [h2]; ring)) (1 / 2 : K) * hd

/-- The actual square root retains its Frobenius phase and the full fifth power. -/
theorem original_odd_sqrt_frobenius_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    u ^ p = u * (1 / 5 : K) ^ ((p - 1) / 2) := by
  calc
    u ^ p = u ^ (2 * ((p - 1) / 2) + 1) :=
      congrArg (fun n : ℕ => u ^ n) (WPFiniteWSource.half_exponent p hp)
    _ = _ := by rw [pow_add, pow_mul, hu, pow_one]; ring

/-- The actual leading coefficient is the original odd-origin value for either square root. -/
theorem actual_odd_infinity_origin_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originalOddInfinityValue (K := K) p = originalROOrigin p u := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hu
    exact (one_div_ne_zero h5) hu.symm
  have hup : u ^ p ≠ 0 := pow_ne_zero p hu0
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have hsquare : (WPFiniteNC122.T0 u) ^ 2 = (121 / 125 : K) := by
    unfold WPFiniteNC122.T0
    rw [div_pow, mul_pow, hu]
    field_simp [h5, h25, h125]
    ring
  have hphase := original_odd_sqrt_frobenius_phase p hp u hu
  have hunit : (5 : K) ^ ((p - 1) / 2) * (1 / 5 : K) ^ ((p - 1) / 2) = 1 := by
    rw [← mul_pow, mul_one_div_cancel h5, one_pow]
  have hscale : (5 : K) / u ^ p * WPFiniteNC122.T0 u =
      -11 * (5 : K) ^ ((p - 1) / 2) := by
    unfold WPFiniteNC122.T0
    linear_combination (norm := (field_simp [h5, hup]; ring))
      (11 * (5 : K) ^ ((p - 1) / 2) / u ^ p) * hphase +
        (11 * u / u ^ p) * hunit
  unfold originalOddInfinityValue originalROOrigin
  rw [oddReciprocalS_origin_coefficient p hp, original_odd_F_source p hp,
    hsquare]
  linear_combination (norm := ring_nf)
    -(oddReciprocalF p : K[X]).eval (121 / 125) * hscale

/-- The original odd-origin harmonic dictionary is now attached to the genuine Os coefficient. -/
theorem actual_odd_infinity_origin_harmonic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    originalOddInfinityValue (K := K) p =
      25 * WPFifthEntropy.C p u - 36 * q2 p +
        11 * (WPFiniteInversion.integerFermatQuotient p 11 : K) := by
  rw [actual_odd_infinity_origin_source p hp u hu]
  exact actual_RO_origin p hp u hu

/-- Both genuine square roots give the same original odd-origin value. -/
theorem actual_odd_origin_root_independent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u v : K) (hu : u ^ 2 = 1 / 5) (hv : v ^ 2 = 1 / 5) :
    originalROOrigin p u = originalROOrigin p v := by
  rw [← actual_odd_infinity_origin_source p hp u hu,
    ← actual_odd_infinity_origin_source p hp v hv]

end WPFieldAssembly.NativeJointSuccessorOddOrigin
