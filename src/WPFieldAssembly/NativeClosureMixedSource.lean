import WPFieldAssembly.ActualBpairBranchSquare
import WPFieldAssembly.GreenLaurentOperators
import WPFiniteCubicJ

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial

namespace WPFieldAssembly.NativeClosureMixedSource

open ActualBpairContraction
open WPFiniteLaurentDifferential

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The odd quotient before its exact Laurent substitution. -/
noncomputable def oddReciprocalF (p : ℕ) : K[X] :=
  ∑ i ∈ Finset.range ((p - 1) / 2),
    Polynomial.C (((2 * i + 1 : ℕ) : K)⁻¹) * Polynomial.X ^ i

noncomputable def oddReciprocalW : K[T;T⁻¹] :=
  LaurentPolynomial.C (((5 : K) ^ 2)⁻¹) *
    WPFiniteWSource.squaredCoordinate.toLaurent * T (-3) * (4 - 11 * T 1) ^ 2

/-- The common finite odd kernel has its original cutoff and every Laurent phase. -/
noncomputable def oddReciprocalKernel (p : ℕ) : K[T;T⁻¹] :=
  ∑ i ∈ Finset.range ((p - 1) / 2),
    LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
      T (-3 * (i : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ i *
          (4 - 11 * T 1) ^ (2 * i + 1)

/-- The branch factor cancels the apparent odd-source denominator as a whole. -/
noncomputable def oddReciprocalJ (p : ℕ) : K[T;T⁻¹] :=
  (branchPolynomial p).toLaurent * WPFiniteWSource.squaredCoordinate.toLaurent *
    oddReciprocalKernel p

/-- The corresponding source before multiplication by the symmetric primitive. -/
noncomputable def oddReciprocalS (p : ℕ) : K[T;T⁻¹] :=
  T ((((p - 1) / 2 - 1 : ℕ) : ℤ)) * oddReciprocalKernel p

noncomputable def frobeniusPhi (p : ℕ) : K[T;T⁻¹] := 4 * T (-(p : ℤ)) - 11

/-- A is arbitrary here; the actual SB72 carrier is substituted only after its release. -/
noncomputable def mixedEvenSource (p : ℕ) (A : K[T;T⁻¹]) (h : K) : K[T;T⁻¹] :=
  invert A - LaurentPolynomial.C (WPFiniteNC122.q p - h) +
    LaurentPolynomial.C (1 / 3 : K) * A

noncomputable def mixedProduct (p : ℕ) (A : K[T;T⁻¹]) (h : K) : K[T;T⁻¹] :=
  oddReciprocalJ p + frobeniusPhi p * Dsym p * mixedEvenSource p A h

noncomputable def mixedResidual (p : ℕ) (A : K[T;T⁻¹]) (h : K) : K[T;T⁻¹] :=
  oddReciprocalS p + WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
    frobeniusPhi p * mixedEvenSource p A h

/-- The full finite numerator retains the deep odd and reciprocal-A phases. -/
noncomputable def mixedJNumerator (p : ℕ) (A : K[T;T⁻¹]) (h : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 5 : K) * (33 - 12 * T 1) * mixedProduct p A h -
    LaurentPolynomial.C (2 * h) * mixedResidual p A h

noncomputable def mixedDelta (p : ℕ) (A : K[T;T⁻¹]) (h : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (2 / 5 : K) * mixedProduct p A h +
    LaurentPolynomial.C (2 / 3 : K) * (Dstar p).toLaurent *
      (invert A - LaurentPolynomial.C (WPFiniteNC122.q p - h))

private theorem D_pow_succ (P : K[T;T⁻¹]) (n : ℕ) :
    D (P ^ (n + 1)) = LaurentPolynomial.C ((n + 1 : ℕ) : K) * P ^ n * D P := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, D_mul, ih]
      simp only [pow_succ]
      have hc : LaurentPolynomial.C ((n + 1 + 1 : ℕ) : K) =
          LaurentPolynomial.C ((n + 1 : ℕ) : K) + 1 := by
        rw [Nat.cast_add, Nat.cast_one, map_add, map_one]
      linear_combination -(P ^ n * P * D P) * hc

private theorem D_eval₂ (P : K[X]) (W : K[T;T⁻¹]) :
    D (P.eval₂ LaurentPolynomial.C W) =
      P.derivative.eval₂ LaurentPolynomial.C W * D W := by
  have hd1 : D (1 : K[T;T⁻¹]) = 0 := by
    simpa only [map_one] using D_C (1 : K)
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.eval₂_add, map_add, hP, hQ, Polynomial.derivative_add,
        Polynomial.eval₂_add]
      ring
  | monomial n c =>
      rw [Polynomial.eval₂_monomial, D_C_mul, Polynomial.derivative_monomial,
        Polynomial.eval₂_monomial]
      cases n with
      | zero => simp only [pow_zero, hd1, Nat.cast_zero, mul_zero, map_zero, zero_mul]
      | succ n =>
          rw [D_pow_succ]
          simp only [Nat.add_sub_cancel, map_mul]
          ring

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

theorem oddReciprocal_denominator_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (i : ℕ) (hi : i < (p - 1) / 2) :
    (5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K) ≠ 0 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hodd : ((2 * i + 1 : ℕ) : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p (2 * i + 1)
      (Finset.mem_Ico.mpr (by omega))
  exact mul_ne_zero (pow_ne_zero _ h5) hodd

theorem oddReciprocal_last_index (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * ((p - 1) / 2 - 1) + 1 = p - 2 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  omega

/-- Every original odd denominator is cancelled separately, including the last one. -/
theorem oddReciprocalF_weighted_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (oddReciprocalF p : K[X]) + Polynomial.C (2 : K) * Polynomial.X *
      (oddReciprocalF p).derivative =
        ∑ i ∈ Finset.range ((p - 1) / 2), (Polynomial.X : K[X]) ^ i := by
  classical
  unfold oddReciprocalF
  rw [Polynomial.derivative_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hu : ((2 * i + 1 : ℕ) : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p (2 * i + 1)
      (Finset.mem_Ico.mpr (by omega))
  have hs : (((2 * i + 1 : ℕ) : K)⁻¹) * (1 + 2 * (i : K)) = 1 := by
    have hc : (1 + 2 * (i : K)) = ((2 * i + 1 : ℕ) : K) := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
    rw [hc, inv_mul_cancel₀ hu]
  have hc := congrArg (Polynomial.C (R := K)) hs
  simp only [map_mul, map_add, map_one] at hc
  rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_X_pow]
  cases i with
  | zero => simp
  | succ j =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ']
      linear_combination (Polynomial.X : K[X]) * Polynomial.X ^ j * hc

/-- The weighted derivative gives the complete finite geometric source. -/
theorem oddReciprocalF_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - Polynomial.X : K[X]) * (oddReciprocalF p +
      Polynomial.C (2 : K) * Polynomial.X * (oddReciprocalF p).derivative) =
        1 - Polynomial.X ^ ((p - 1) / 2) := by
  rw [oddReciprocalF_weighted_derivative p hp]
  rw [mul_comm, geom_sum_mul_neg]

/-- The original odd cutoff evaluates to the same Fermat quotient q. -/
theorem oddReciprocalF_eval_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (oddReciprocalF p : K[X]).eval 1 = WPFiniteNC122.q p := by
  let N := (p - 1) / 2
  have hpn : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hfull : (∑ j ∈ Finset.Ico 1 p, (j : K)⁻¹) = 0 := by
    simpa only [WPFiniteField.ell, one_pow, one_div] using
      (WPFiniteCubicJ.rational_ell_sources (K := K) p hp).1
  have heven : (∑ j ∈ Finset.Ico 1 (N + 1), ((2 * j : ℕ) : K)⁻¹) =
      (1 / 2 : K) * WPFiniteJSource.H N := by
    unfold WPFiniteJSource.H
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, Nat.cast_ofNat, mul_inv_rev, one_div]
    ring
  have hpair := sum_full_odd_ranges (fun j => (j : K)⁻¹) N
  rw [← hpn, hfull, heven, WPFiniteJSource.H_half_eq_quotient p hp] at hpair
  have hc : (1 / 2 : K) * 2 = 1 := one_div_mul_cancel h2
  simp only [oddReciprocalF, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]
  change (∑ i ∈ Finset.range N, ((2 * i + 1 : ℕ) : K)⁻¹) = WPFiniteNC122.q p
  linear_combination -hpair + WPFiniteNC122.q p * hc

/-- The literal Laurent kernel is the odd quotient at the full reciprocal cubic argument. -/
theorem oddReciprocalKernel_substitution (p : ℕ) :
    (oddReciprocalKernel p : K[T;T⁻¹]) = (4 - 11 * T 1) *
      (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW := by
  classical
  unfold oddReciprocalKernel oddReciprocalF
  rw [Polynomial.eval₂_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : ((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹ =
      ((5 : K) ^ 2)⁻¹ ^ i * (((2 * i + 1 : ℕ) : K)⁻¹) := by
    rw [mul_inv_rev, pow_mul, inv_pow]
    ring
  rw [hs]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, oddReciprocalW, map_mul, map_pow, mul_pow,
    LaurentPolynomial.T_pow]
  rw [pow_succ (4 - 11 * T 1 : K[T;T⁻¹]) (2 * i), ← pow_mul,
    mul_comm (i : ℤ) (-3 : ℤ)]
  ring

private theorem geometric_source_eval (F G : K[X]) (n : ℕ) (W : K[T;T⁻¹])
    (hsource : (1 - Polynomial.X) * (F + 2 * Polynomial.X * G) =
      1 - Polynomial.X ^ n) :
    (1 - W) * (F.eval₂ LaurentPolynomial.C W +
      2 * W * G.eval₂ LaurentPolynomial.C W) = 1 - W ^ n := by
  have he := congrArg (Polynomial.eval₂RingHom LaurentPolynomial.C W) hsource
  simpa only [_root_.map_mul, _root_.map_sub, _root_.map_add, _root_.map_one,
    _root_.map_pow, _root_.map_ofNat, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X] using he

/-- The cleared finite source remains exact at the reciprocal Laurent cubic. -/
theorem oddReciprocalKernel_geometric_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - (oddReciprocalW : K[T;T⁻¹])) *
      ((oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW +
        2 * oddReciprocalW *
          (oddReciprocalF p).derivative.eval₂ LaurentPolynomial.C oddReciprocalW) =
            1 - oddReciprocalW ^ ((p - 1) / 2) := by
  exact geometric_source_eval (oddReciprocalF p) (oddReciprocalF p).derivative
    ((p - 1) / 2) oddReciprocalW (oddReciprocalF_cleared_source p hp)

/-- The chain rule retains the entire geometric source and introduces no derivative division. -/
theorem oddReciprocalKernel_geometric_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - (oddReciprocalW : K[T;T⁻¹])) *
      (D oddReciprocalW * (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW +
        2 * oddReciprocalW *
          D ((oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW)) =
            D oddReciprocalW * (1 - oddReciprocalW ^ ((p - 1) / 2)) := by
  rw [D_eval₂]
  linear_combination D (oddReciprocalW (K := K)) *
    oddReciprocalKernel_geometric_source (K := K) p hp

/-- The reciprocal cubic denominator factors without discarding any Frobenius phase. -/
theorem oddReciprocalW_cubic_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (1 - oddReciprocalW : K[T;T⁻¹]) = LaurentPolynomial.C (1 / 125 : K) *
      T (-3) * (4 * T 1 - 1) * (4 - T 1) ^ 2 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hc : LaurentPolynomial.C (1 / 125 : K) * 125 = (1 : K[T;T⁻¹]) := by
    change LaurentPolynomial.C (1 / 125 : K) * LaurentPolynomial.C (125 : K) = 1
    rw [← map_mul, one_div_mul_cancel h125, map_one]
  have ht : (T 3 * T (-3) : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  have ht0 : (T 3 : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at ht
    exact zero_ne_one ht
  have ht3 : (T 1 : K[T;T⁻¹]) ^ 3 = T 3 := by
    rw [LaurentPolynomial.T_pow]
    norm_num
  have hs : LaurentPolynomial.C (((5 : K) ^ 2)⁻¹) *
      WPFiniteWSource.squaredCoordinate.toLaurent =
        LaurentPolynomial.C (1 / 125 : K) * (T 1 + 1) := by
    have hscalar : ((5 : K) ^ 2)⁻¹ * (5 : K)⁻¹ = (1 / 125 : K) := by
      rw [one_div, ← mul_inv_rev]
      congr 1
      ring
    simp only [WPFiniteWSource.squaredCoordinate, map_mul,
      Polynomial.toLaurent_C, map_add, Polynomial.toLaurent_X, map_one]
    rw [← mul_assoc, ← map_mul, hscalar]
  have hw : (oddReciprocalW : K[T;T⁻¹]) =
      LaurentPolynomial.C (1 / 125 : K) * (T 1 + 1) * T (-3) *
        (4 - 11 * T 1) ^ 2 := by
    rw [oddReciprocalW, hs]
  have hcube : (125 * (T 1) ^ 3 - (T 1 + 1) * (4 - 11 * T 1) ^ 2 :
      K[T;T⁻¹]) = (4 * T 1 - 1) * (4 - T 1) ^ 2 := by ring
  apply mul_left_cancel₀ ht0
  calc
    _ = T 3 - LaurentPolynomial.C (1 / 125 : K) * (T 1 + 1) *
        (4 - 11 * T 1) ^ 2 := by
      rw [hw]
      linear_combination -LaurentPolynomial.C (1 / 125 : K) * (T 1 + 1) *
        (4 - 11 * T 1) ^ 2 * ht
    _ = LaurentPolynomial.C (1 / 125 : K) * (4 * T 1 - 1) *
        (4 - T 1) ^ 2 := by
      rw [← ht3]
      linear_combination LaurentPolynomial.C (1 / 125 : K) * hcube - (T 1) ^ 3 * hc
    _ = _ := by
      linear_combination -LaurentPolynomial.C (1 / 125 : K) * (4 * T 1 - 1) *
        (4 - T 1) ^ 2 * ht

/-- The reciprocal cubic's literal derivative keeps its negative-four monomial. -/
theorem oddReciprocalW_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    D (oddReciprocalW : K[T;T⁻¹]) = LaurentPolynomial.C (3 / 125 : K) *
      T (-4) * (4 - 11 * T 1) * (T 1 - 4) := by
  have hd1 : D (1 : K[T;T⁻¹]) = 0 := by simpa only [map_one] using D_C (1 : K)
  have hd4 : D (4 : K[T;T⁻¹]) = 0 := by
    simpa only [map_ofNat] using D_C (4 : K)
  have hdt : D (T 1 : K[T;T⁻¹]) = 1 := by
    simpa using D_monomial (1 : K) 1
  have hdm : D (T (-3) : K[T;T⁻¹]) = -3 * T (-4) := by
    simpa [map_ofNat] using D_monomial (1 : K) (-3)
  have hdl : D (4 * T 1 - 1 : K[T;T⁻¹]) = 4 := by
    rw [map_sub, D_mul, hd4, hdt, hd1]
    ring
  have hdz : D (4 - T 1 : K[T;T⁻¹]) = -1 := by
    rw [map_sub, hd4, hdt, zero_sub]
  have hdz2 : D ((4 - T 1 : K[T;T⁻¹]) ^ 2) = -2 * (4 - T 1) := by
    rw [pow_two, D_mul, hdz]
    ring
  have ht : (T 1 * T (-4) : K[T;T⁻¹]) = T (-3) := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  have hs : LaurentPolynomial.C (3 / 125 : K) =
      3 * LaurentPolynomial.C (1 / 125 : K) := by
    rw [show (3 / 125 : K) = 3 * (1 / 125) by ring, map_mul, map_ofNat]
  have hw : (oddReciprocalW : K[T;T⁻¹]) = 1 -
      LaurentPolynomial.C (1 / 125 : K) *
        (T (-3) * (4 * T 1 - 1) * (4 - T 1) ^ 2) := by
    linear_combination -oddReciprocalW_cubic_factor (K := K) p hp
  rw [hw, map_sub, hd1, D_C_mul, D_mul, D_mul, hdm, hdl, hdz2, hs]
  linear_combination -LaurentPolynomial.C (1 / 125 : K) *
    (-4 * (4 - T 1) ^ 2 + 2 * (4 * T 1 - 1) * (4 - T 1)) * ht

/-- This is precisely the finite branch-cancelled R_O reciprocal source. -/
theorem oddReciprocalJ_literal (p : ℕ) : (oddReciprocalJ p : K[T;T⁻¹]) =
    (branchPolynomial p).toLaurent *
      ∑ i ∈ Finset.range ((p - 1) / 2),
        LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
          T (-3 * (i : ℤ)) *
            WPFiniteWSource.squaredCoordinate.toLaurent ^ (i + 1) *
              (4 - 11 * T 1) ^ (2 * i + 1) := by
  unfold oddReciprocalJ oddReciprocalKernel
  rw [mul_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

/-- The same kernel gives the complete s^N R_O reciprocal, without negative truncation. -/
theorem oddReciprocalS_literal (p : ℕ) (hp : 19 ≤ p) : (oddReciprocalS p : K[T;T⁻¹]) =
    ∑ i ∈ Finset.range ((p - 1) / 2),
      LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
        T ((((p - 1) / 2 : ℕ) : ℤ) - 3 * (i : ℤ) - 1) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ i *
            (4 - 11 * T 1) ^ (2 * i + 1) := by
  unfold oddReciprocalS oddReciprocalKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have ht : (T ((((p - 1) / 2 - 1 : ℕ) : ℤ)) * T (-3 * (i : ℤ)) :
      K[T;T⁻¹]) = T ((((p - 1) / 2 : ℕ) : ℤ) - 3 * (i : ℤ) - 1) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  linear_combination
    LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ i *
        (4 - 11 * T 1) ^ (2 * i + 1) * ht

/-- The cleared derivative belongs to the reciprocal odd source itself, with every phase intact. -/
theorem oddReciprocalS_cleared_geometric_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent * D (oddReciprocalS p) +
        LaurentPolynomial.C (1 / 10 : K) * oddReciprocalS p) =
          LaurentPolynomial.C (75 / 2 : K) * T ((((p - 1) / 2 + 1 : ℕ) : ℤ)) *
            ((oddReciprocalW : K[T;T⁻¹]) ^ ((p - 1) / 2) - 1) := by
  let N := (p - 1) / 2
  let m := N - 1
  let x : K[T;T⁻¹] := T 1
  let t : K[T;T⁻¹] := T ((m : ℤ) - 1)
  let z : K[T;T⁻¹] := 4 - 11 * x
  let b : K[T;T⁻¹] := (4 * x - 1) * (4 - x) ^ 2
  let F : K[T;T⁻¹] := (oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW
  let F' : K[T;T⁻¹] := (oddReciprocalF p).derivative.eval₂ LaurentPolynomial.C oddReciprocalW
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hn : 2 * N + 1 = p := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    dsimp [N]
    omega
  have hm : (m : K) = -3 / 2 := by
    have hc := congrArg (fun n : ℕ => (n : K)) hn
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      CharP.cast_eq_zero] at hc
    have hmN : (m : K) = (N : K) - 1 := by
      dsimp [m]
      rw [Nat.cast_sub (by dsimp [N]; omega), Nat.cast_one]
    apply (eq_div_iff h2).2
    linear_combination hc + 2 * hmN
  have hs : WPFiniteWSource.squaredCoordinate.toLaurent =
      LaurentPolynomial.C (1 / 5 : K) * (x + 1) := by
    simp only [WPFiniteWSource.squaredCoordinate, map_mul, Polynomial.toLaurent_C,
      map_add, Polynomial.toLaurent_X, map_one, one_div, x]
  have ha : (WPFiniteZSource.Abar : K[X]).toLaurent = (4 - x) * (4 * x - 1) := by
    simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one, x]
  have hxt : x * t = (T (m : ℤ) : K[T;T⁻¹]) := by
    dsimp [x, t]
    rw [← T_add]
    congr 1
    omega
  have hxt3 : x ^ 3 * t = (T ((N + 1 : ℕ) : ℤ) : K[T;T⁻¹]) := by
    dsimp [x, t, m, N]
    rw [T_pow, ← T_add]
    congr 1
    omega
  have hneg : x * (T (-4) : K[T;T⁻¹]) = T (-3) := by
    dsimp [x]
    rw [← T_add]
    norm_num
  have hDtm : D (T (m : ℤ) : K[T;T⁻¹]) = LaurentPolynomial.C (m : K) * t := by
    simpa only [map_one, one_mul, Int.cast_natCast, t] using D_monomial (1 : K) (m : ℤ)
  have hDz : D z = (-11 : K[T;T⁻¹]) := by
    have hd4 : D (4 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (4 : K)
    have hd11 : D (11 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (11 : K)
    have hdx : D x = (1 : K[T;T⁻¹]) := by simpa [x] using D_monomial (1 : K) 1
    dsimp [z]
    rw [map_sub, D_mul, hd4, hd11, hdx]
    ring
  have hOs : (oddReciprocalS p : K[T;T⁻¹]) = T (m : ℤ) * z * F := by
    rw [oddReciprocalS, oddReciprocalKernel_substitution]
    change T (m : ℤ) * (z * F) = T (m : ℤ) * z * F
    ring
  have hDOs : D (oddReciprocalS p : K[T;T⁻¹]) =
      (LaurentPolynomial.C (m : K) * t * z - 11 * T (m : ℤ)) * F +
        T (m : ℤ) * z * F' * D oddReciprocalW := by
    rw [hOs, D_mul, D_mul, hDtm, hDz, D_eval₂]
    ring
  have hc1 : LaurentPolynomial.C (1 / 5 : K) * LaurentPolynomial.C (-3 / 2 : K) =
      -3 * LaurentPolynomial.C (1 / 10 : K) := by
    have hc : (1 / 5 : K) * (-3 / 2) = -3 * (1 / 10) := by field_simp [h2, h5, h10]; ring
    simpa only [map_mul, map_neg, map_ofNat] using congrArg (LaurentPolynomial.C (R := K)) hc
  have hc2 : (11 : K[T;T⁻¹]) * LaurentPolynomial.C (1 / 5 : K) =
      22 * LaurentPolynomial.C (1 / 10 : K) := by
    have hc : (11 : K) * (1 / 5) = 22 * (1 / 10) := by field_simp [h5, h10]; ring
    simpa only [map_mul, map_ofNat] using congrArg (LaurentPolynomial.C (R := K)) hc
  have hc3 : LaurentPolynomial.C (3 / 10 : K) = 3 * LaurentPolynomial.C (1 / 10 : K) := by
    rw [show (3 / 10 : K) = 3 * (1 / 10) by ring, map_mul, map_ofNat]
  have hfirst : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent *
        (LaurentPolynomial.C (m : K) * z - 11 * x) +
          LaurentPolynomial.C (1 / 10 : K) * x * z) =
            -LaurentPolynomial.C (3 / 10 : K) * b := by
    rw [ha, hs, hm, hc3]
    dsimp [z, b]
    linear_combination (4 - x) * (4 * x - 1) * (x + 1) * (4 - 11 * x) * hc1 -
      (4 - x) * (4 * x - 1) * (x + 1) * x * hc2
  have hw : (oddReciprocalW : K[T;T⁻¹]) = LaurentPolynomial.C (1 / 125 : K) *
      (x + 1) * T (-3) * z ^ 2 := by
    have hc : ((5 : K) ^ 2)⁻¹ * (1 / 5) = (1 / 125 : K) := by
      field_simp [h5, h125]; ring
    rw [oddReciprocalW, hs]
    dsimp [z, x]
    rw [← mul_assoc, ← map_mul, hc]
  have hc4 : LaurentPolynomial.C (1 / 5 : K) * LaurentPolynomial.C (3 / 125 : K) =
      2 * LaurentPolynomial.C (3 / 10 : K) * LaurentPolynomial.C (1 / 125 : K) := by
    have hc : (1 / 5 : K) * (3 / 125) = 2 * (3 / 10) * (1 / 125) := by
      field_simp [h5, h10, h125]; ring
    simpa only [map_mul, map_ofNat] using congrArg (LaurentPolynomial.C (R := K)) hc
  have hsecond : (WPFiniteZSource.Abar : K[X]).toLaurent *
      WPFiniteWSource.squaredCoordinate.toLaurent * T (m : ℤ) * z * D oddReciprocalW =
        -LaurentPolynomial.C (3 / 10 : K) * t * b * 2 * oddReciprocalW := by
    rw [ha, hs, oddReciprocalW_derivative (K := K) p hp, hw, ← hxt]
    dsimp [z, b]
    linear_combination (4 - x) * (4 * x - 1) * (x + 1) * x * t *
        (4 - 11 * x) ^ 2 * T (-4) * (x - 4) * hc4 -
      2 * LaurentPolynomial.C (3 / 10 : K) * LaurentPolynomial.C (1 / 125 : K) *
        t * (4 * x - 1) * (4 - x) ^ 2 * (x + 1) * (4 - 11 * x) ^ 2 * hneg
  have hcol : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent * D (oddReciprocalS p) +
        LaurentPolynomial.C (1 / 10 : K) * oddReciprocalS p) =
          -LaurentPolynomial.C (3 / 10 : K) * t * b * (F + 2 * oddReciprocalW * F') := by
    have hsecond' := hsecond
    rw [← hxt] at hsecond'
    rw [hDOs, hOs, ← hxt]
    linear_combination t * F * hfirst + F' * hsecond'
  have h75 : LaurentPolynomial.C (75 / 2 : K) * LaurentPolynomial.C (1 / 125 : K) =
      LaurentPolynomial.C (3 / 10 : K) := by
    rw [← map_mul]
    congr 1
    field_simp [h2, h10, h125]; ring
  have hcb : LaurentPolynomial.C (75 / 2 : K) * T ((N + 1 : ℕ) : ℤ) *
      (1 - oddReciprocalW) = LaurentPolynomial.C (3 / 10 : K) * t * b := by
    rw [oddReciprocalW_cubic_factor (K := K) p hp, ← hxt3]
    have ht : (x ^ 3 * T (-3) : K[T;T⁻¹]) = 1 := by
      dsimp [x]
      rw [T_pow, ← T_add]
      norm_num
    dsimp [b, x]
    linear_combination (T 1) ^ 3 * t * T (-3) * (4 * T 1 - 1) * (4 - T 1) ^ 2 * h75 +
      LaurentPolynomial.C (3 / 10 : K) * t * (4 * T 1 - 1) * (4 - T 1) ^ 2 * ht
  have hgeo := oddReciprocalKernel_geometric_source (K := K) p hp
  change (1 - oddReciprocalW) * (F + 2 * oddReciprocalW * F') = 1 - oddReciprocalW ^ N at hgeo
  change _ = LaurentPolynomial.C (75 / 2 : K) * T ((N + 1 : ℕ) : ℤ) * (oddReciprocalW ^ N - 1)
  linear_combination hcol + (F + 2 * oddReciprocalW * F') * hcb -
    LaurentPolynomial.C (75 / 2 : K) * T ((N + 1 : ℕ) : ℤ) * hgeo

/-- The original odd source keeps its complete Frobenius power and lowest exponent. -/
theorem oddReciprocalS_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent * D (oddReciprocalS p) +
        LaurentPolynomial.C (1 / 10 : K) * oddReciprocalS p) =
          LaurentPolynomial.C (75 / 2 : K) *
            (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
                T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) -
              T ((((p - 1) / 2 + 1 : ℕ) : ℤ))) := by
  let N := (p - 1) / 2
  have h2N : 2 * N = p - 1 := by
    have hpN := WPFiniteWSource.half_exponent p hp
    dsimp [N]
    omega
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h5p : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  have h5pow : (5 : K) ^ (p - 1) = 1 := by
    apply mul_right_cancel₀ h5
    rw [← pow_succ, show p - 1 + 1 = p by omega, one_mul]
    exact h5p
  have hi : (((5 : K) ^ 2)⁻¹) ^ N = 1 := by
    calc
      _ = (((5 : K) ^ 2) ^ N)⁻¹ := by simp only [inv_pow]
      _ = 1 := by rw [← pow_mul, h2N, h5pow, inv_one]
  have hwN : (oddReciprocalW : K[T;T⁻¹]) ^ N =
      WPFiniteWSource.squaredCoordinate.toLaurent ^ N * T (-3 * (N : ℤ)) *
        (4 - 11 * T 1) ^ (p - 1) := by
    rw [oddReciprocalW, mul_pow, mul_pow, mul_pow, ← map_pow, hi,
      map_one, one_mul, T_pow, ← pow_mul, h2N]
    rw [mul_comm (N : ℤ) (-3 : ℤ)]
  have ht : (T ((N + 1 : ℕ) : ℤ) * T (-3 * (N : ℤ)) : K[T;T⁻¹]) =
      T (2 - (p : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  rw [oddReciprocalS_cleared_geometric_source (K := K) p hp]
  change LaurentPolynomial.C (75 / 2 : K) * T ((N + 1 : ℕ) : ℤ) *
    (oddReciprocalW ^ N - 1) = _
  rw [hwN]
  linear_combination LaurentPolynomial.C (75 / 2 : K) *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ N * (4 - 11 * T 1) ^ (p - 1) * ht

/-- At w=1 the literal source uses its complete odd harmonic endpoint. -/
theorem oddReciprocalS_eval (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (a : K) (ha : a ≠ 0)
    (hN : a ^ ((p - 1) / 2) = 1)
    (hw : GreenLaurentOperators.ev a ha (oddReciprocalW : K[T;T⁻¹]) = 1) :
    GreenLaurentOperators.ev a ha (oddReciprocalS p : K[T;T⁻¹]) =
      a⁻¹ * (4 - 11 * a) * WPFiniteNC122.q p := by
  let φ := GreenLaurentOperators.ev a ha
  have hW : φ (oddReciprocalW : K[T;T⁻¹]) = 1 := hw
  have hC (c : K) : φ (LaurentPolynomial.C c) = c := by
    simp [φ, GreenLaurentOperators.ev]
  have hX : φ (T 1) = a := by simp [φ, GreenLaurentOperators.ev]
  have hF : φ ((oddReciprocalF p).eval₂ LaurentPolynomial.C oddReciprocalW) =
      WPFiniteNC122.q p := by
    rw [← oddReciprocalF_eval_one (K := K) p hp]
    simp only [oddReciprocalF, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      map_sum, map_mul, map_pow, hC, hW, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, mul_one]
  have hm : ((p - 1) / 2 - 1) + 1 = (p - 1) / 2 := by omega
  have ht : φ (T ((((p - 1) / 2 - 1 : ℕ) : ℤ))) = a⁻¹ := by
    have he : a ^ ((p - 1) / 2 - 1) = a⁻¹ := by
      apply mul_right_cancel₀ ha
      rw [← pow_succ, hm, hN, inv_mul_cancel₀ ha]
    simpa [φ, GreenLaurentOperators.ev, Units.val_zpow_eq_zpow_val] using he
  change φ (oddReciprocalS p) = _
  rw [oddReciprocalS, oddReciprocalKernel_substitution, map_mul, map_mul, ht, hF]
  simp only [map_sub, map_mul, map_ofNat, hX]
  ring

/-- Both original branch endpoints use w=1; no value is inferred from a vanished derivative. -/
theorem oddReciprocalS_eval_four (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (h4 : (4 : K) ≠ 0) :
    GreenLaurentOperators.ev 4 h4 (oddReciprocalS p : K[T;T⁻¹]) =
      -10 * WPFiniteNC122.q p := by
  have hw : GreenLaurentOperators.ev 4 h4 (oddReciprocalW : K[T;T⁻¹]) = 1 := by
    have hc := congrArg (GreenLaurentOperators.ev (4 : K) h4)
      (oddReciprocalW_cubic_factor (K := K) p hp)
    have ht : GreenLaurentOperators.ev 4 h4 (T 1 : K[T;T⁻¹]) = 4 := by
      simp [GreenLaurentOperators.ev]
    simp only [map_sub, map_one, map_mul, map_pow, map_ofNat, ht,
      sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero] at hc
    linear_combination -hc
  rw [oddReciprocalS_eval p hp 4 h4 (WPFiniteWSource.four_half_power p hp) hw]
  field_simp [h4]
  ring

theorem oddReciprocalS_eval_quarter (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (h4 : (4 : K) ≠ 0) :
    GreenLaurentOperators.ev (1 / 4) (one_div_ne_zero h4)
      (oddReciprocalS p : K[T;T⁻¹]) = 5 * WPFiniteNC122.q p := by
  have hr : (4 : K) * (1 / 4) - 1 = 0 := by rw [mul_one_div_cancel h4, sub_self]
  have hw : GreenLaurentOperators.ev (1 / 4) (one_div_ne_zero h4)
      (oddReciprocalW : K[T;T⁻¹]) = 1 := by
    have hc := congrArg (GreenLaurentOperators.ev (1 / 4 : K) (one_div_ne_zero h4))
      (oddReciprocalW_cubic_factor (K := K) p hp)
    have ht : GreenLaurentOperators.ev (1 / 4) (one_div_ne_zero h4)
        (T 1 : K[T;T⁻¹]) = (1 / 4 : K) := by simp [GreenLaurentOperators.ev]
    simp only [map_sub, map_one, map_mul, map_pow, map_ofNat, ht, hr,
      mul_zero, zero_mul] at hc
    linear_combination -hc
  have hN : (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
    calc
      _ = ((4 : K) ^ ((p - 1) / 2))⁻¹ := by simp only [one_div, inv_pow]
      _ = 1 := by rw [WPFiniteWSource.four_half_power p hp, inv_one]
  rw [oddReciprocalS_eval p hp (1 / 4) (one_div_ne_zero h4) hN hw]
  field_simp [h4]
  ring

/-- The genuine branch factor identifies both odd products before any residue calculation. -/
theorem oddReciprocal_product (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (oddReciprocalJ p : K[T;T⁻¹]) = Dsym p * oddReciprocalS p := by
  have hf := congrArg (fun P : K[X] => P.toLaurent)
    (branchPolynomial_factor (K := K) p hp)
  rw [branchNumerator_toLaurent p hp] at hf
  simp only [map_mul, map_pow] at hf
  unfold oddReciprocalJ oddReciprocalS
  rw [pow_succ] at hf
  linear_combination -oddReciprocalKernel (K := K) p * hf

/-- No division by Dsym and no deletion of Laurent phases is used in this identity. -/
theorem mixedProduct_consistency (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (A : K[T;T⁻¹]) (h : K) :
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      mixedProduct p A h = Dsym p * mixedResidual p A h := by
  unfold mixedProduct mixedResidual
  linear_combination oddReciprocal_product (K := K) p hp

theorem mixedHalfPower_homogeneous (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    WPFiniteWSource.squaredCoordinate.toLaurent *
        D (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) +
      LaurentPolynomial.C (1 / 10 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) = 0 := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have hNpos : 0 < N := by dsimp [N]; omega
  have hN : (N : K) = -1 / 2 := by
    have hc := congrArg (fun n : ℕ => (n : K)) (WPFiniteWSource.half_exponent p hp)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      CharP.cast_eq_zero] at hc
    change 0 = 2 * (N : K) + 1 at hc
    apply (eq_div_iff h2).2
    change (N : K) * 2 = -1
    linear_combination -hc
  have hs : D s = LaurentPolynomial.C (1 / 5 : K) := by
    dsimp only [s]
    rw [D_toLaurent]
    simp [WPFiniteWSource.squaredCoordinate, one_div]
  have hD := D_pow_succ s (N - 1)
  rw [show N - 1 + 1 = N by omega, hs] at hD
  have hpow : s ^ N = s ^ (N - 1) * s := by
    rw [← pow_succ, show N - 1 + 1 = N by omega]
  have hcoef : LaurentPolynomial.C (N : K) * LaurentPolynomial.C (1 / 5 : K) +
      LaurentPolynomial.C (1 / 10 : K) = (0 : K[T;T⁻¹]) := by
    rw [← map_mul, ← map_add, hN]
    have he : (-1 / 2 : K) * (1 / 5) + 1 / 10 = 0 := by
      field_simp [h2, h5, h10]
      ring
    rw [he, map_zero]
  change s * D (s ^ N) + LaurentPolynomial.C (1 / 10 : K) * s ^ N = 0
  rw [hD, hpow]
  linear_combination s ^ (N - 1) * s * hcoef

private theorem frobeniusPhi_derivative_zero (p : ℕ) [Fact p.Prime] [CharP K p] :
    D (frobeniusPhi p : K[T;T⁻¹]) = 0 := by
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have ht : D (T (-(p : ℤ)) : K[T;T⁻¹]) = 0 := by
    simpa only [map_one, one_mul, Int.cast_neg, Int.cast_natCast, hpK,
      neg_zero, map_zero, zero_mul] using D_monomial (1 : K) (-(p : ℤ))
  have h4 : D (4 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (4 : K)
  have h11 : D (11 : K[T;T⁻¹]) = 0 := by simpa only [map_ofNat] using D_C (11 : K)
  rw [frobeniusPhi, map_sub, D_mul, h4, h11, ht]
  ring

/-- The full mixed source follows from both whole A derivatives, with every phase retained. -/
theorem mixedResidual_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (A : K[T;T⁻¹]) (h : K)
    (hA : (WPFiniteZSource.Abar : K[X]).toLaurent * D A =
      LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (4 * T (p : ℤ) - 11)))
    (hAv : (WPFiniteZSource.Abar : K[X]).toLaurent * D (invert A) =
      -LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p)) :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
      (WPFiniteWSource.squaredCoordinate.toLaurent * D (mixedResidual p A h) +
        LaurentPolynomial.C (1 / 10 : K) * mixedResidual p A h) =
      LaurentPolynomial.C (75 / 2 : K) *
        (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
            T (2 - (p : ℤ)) * (4 - 11 * T 1) ^ (p - 1) -
          T ((((p - 1) / 2 + 1 : ℕ) : ℤ))) +
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) * frobeniusPhi p *
        (-LaurentPolynomial.C (3 / 2 : K) *
          ((4 * T (-1) - 11) - T (-(((p - 1) / 2 : ℕ) : ℤ)) *
            WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) * frobeniusPhi p) +
          LaurentPolynomial.C (1 / 2 : K) *
            ((4 * T 1 - 11) - WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
              (4 * T (p : ℤ) - 11))) := by
  let N := (p - 1) / 2
  let s : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent
  let B : K[T;T⁻¹] := (WPFiniteZSource.Abar : K[X]).toLaurent
  let M : K[T;T⁻¹] := mixedEvenSource p A h
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h32 : LaurentPolynomial.C (1 / 3 : K) * LaurentPolynomial.C (3 / 2 : K) =
      (LaurentPolynomial.C (1 / 2 : K) : K[T;T⁻¹]) := by
    rw [← map_mul]
    congr 1
    simp only [div_eq_mul_inv, one_mul]
    rw [← mul_assoc, inv_mul_cancel₀ h3, one_mul]
  have hM : D M = D (invert A) + LaurentPolynomial.C (1 / 3 : K) * D A := by
    simp only [M, mixedEvenSource, map_add, map_sub, D_C, sub_zero, D_C_mul]
  have hhom := mixedHalfPower_homogeneous (K := K) p hp
  change s * D (s ^ N) + LaurentPolynomial.C (1 / 10 : K) * s ^ N = 0 at hhom
  have hphi := frobeniusPhi_derivative_zero (K := K) p
  have hD : D (mixedResidual p A h) = D (oddReciprocalS p) +
      D (s ^ N) * frobeniusPhi p * M + s ^ N * frobeniusPhi p * D M := by
    simp only [mixedResidual, map_add, D_mul, hphi, mul_zero, add_zero, N, s, M]
    ring
  have hsplit : B * (s * D (mixedResidual p A h) +
      LaurentPolynomial.C (1 / 10 : K) * mixedResidual p A h) =
      B * (s * D (oddReciprocalS p) + LaurentPolynomial.C (1 / 10 : K) * oddReciprocalS p) +
        s ^ (N + 1) * frobeniusPhi p * (B * D M) := by
    rw [hD, mixedResidual]
    change B * (s * (D (oddReciprocalS p) +
      D (s ^ N) * frobeniusPhi p * M + s ^ N * frobeniusPhi p * D M) +
      LaurentPolynomial.C (1 / 10 : K) * (oddReciprocalS p + s ^ N * frobeniusPhi p * M)) = _
    rw [pow_succ]
    linear_combination B * frobeniusPhi p * M * hhom
  have hBM : B * D M =
      -LaurentPolynomial.C (3 / 2 : K) *
        ((4 * T (-1) - 11) - T (-(N : ℤ)) * s ^ N * frobeniusPhi p) +
      LaurentPolynomial.C (1 / 2 : K) *
        ((4 * T 1 - 11) - s ^ N * (4 * T (p : ℤ) - 11)) := by
    rw [hM, mul_add]
    calc
      _ = B * D (invert A) + LaurentPolynomial.C (1 / 3 : K) * (B * D A) := by ring
      _ = _ := by rw [hA, hAv]; rw [← mul_assoc, h32]
  change B * (s * D (mixedResidual p A h) +
    LaurentPolynomial.C (1 / 10 : K) * mixedResidual p A h) = _
  rw [hsplit, hBM, oddReciprocalS_cleared_source p hp]

/-- Literal term bounds give the whole odd-source band, before any cancellation. -/
theorem oddReciprocalS_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (j : ℤ) (hj : j ∈ (oddReciprocalS p : K[T;T⁻¹]).coeff.support) :
    -(p : ℤ) + 3 ≤ j ∧ j ≤ ((p - 1) / 2 : ℕ) := by
  let N := (p - 1) / 2
  let s : K[X] := WPFiniteWSource.squaredCoordinate
  let z : K[X] := 4 - 11 * Polynomial.X
  have hN : 0 < N := by dsimp [N]; omega
  have hpN : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have hsdegree : s.natDegree ≤ 1 := by
    dsimp [s, WPFiniteWSource.squaredCoordinate]
    simpa only [zero_add] using Polynomial.natDegree_mul_le_of_le
      (show (Polynomial.C ((5 : K)⁻¹)).natDegree ≤ 0 by simp)
      ((Polynomial.natDegree_add_le _ _).trans (by simp) :
        (Polynomial.X + 1 : K[X]).natDegree ≤ 1)
  have hzdegree : z.natDegree ≤ 1 := by
    have hlin : (11 * Polynomial.X : K[X]).natDegree ≤ 1 := by
      simpa only [zero_add] using Polynomial.natDegree_mul_le_of_le
        (show (11 : K[X]).natDegree ≤ 0 by simp) (Polynomial.natDegree_X_le (R := K))
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hlin)
  have hzmap : z.toLaurent = (4 - 11 * T 1 : K[T;T⁻¹]) := by
    simp only [z, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X]
  have hs := Above_toLaurent s 1 hsdegree
  have hz : Above (4 - 11 * T 1 : K[T;T⁻¹]) 1 := by
    rw [← hzmap]
    exact Above_toLaurent z 1 hzdegree
  have hsInv := Above_invert_toLaurent s
  have hzInv : Above (invert (4 - 11 * T 1 : K[T;T⁻¹])) 0 := by
    rw [← hzmap]
    exact Above_invert_toLaurent z
  have hkernel : Above (oddReciprocalKernel p : K[T;T⁻¹]) 1 := by
    intro k hk
    rw [oddReciprocalKernel, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have ht := Above_mul
      (Above_mul (Above_monomial
        (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) (-3 * (i : ℤ)))
        (Above_pow hs i)) (Above_pow hz (2 * i + 1))
    have ht' : Above
        (LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
          T (-3 * (i : ℤ)) * s.toLaurent ^ i * (4 - 11 * T 1) ^ (2 * i + 1)) 1 := by
      convert ht using 1
      all_goals
        push_cast
        ring
    exact ht' k hk
  have hkernelInv : Above (invert (oddReciprocalKernel p : K[T;T⁻¹]))
      (3 * ((N - 1 : ℕ) : ℤ)) := by
    intro k hk
    rw [oddReciprocalKernel, map_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have ht : Above
        (invert (LaurentPolynomial.C (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) *
          T (-3 * (i : ℤ)) * s.toLaurent ^ i * (4 - 11 * T 1) ^ (2 * i + 1)))
        (3 * (i : ℤ)) := by
      simp only [map_mul, map_pow, invert_C, invert_T, neg_mul, neg_neg]
      have hb := Above_mul
        (Above_mul (Above_monomial
          (((5 : K) ^ (2 * i) * ((2 * i + 1 : ℕ) : K))⁻¹) (3 * (i : ℤ)))
          (Above_pow hsInv i)) (Above_pow hzInv (2 * i + 1))
      convert hb using 1
      all_goals
        push_cast
        ring
    exact ht k (by omega)
  have hOs : Above (oddReciprocalS p : K[T;T⁻¹]) (N : ℤ) := by
    unfold oddReciprocalS
    have he := Above_shift hkernel ((N - 1 : ℕ) : ℤ)
    convert he using 1
    all_goals omega
  have hOsInv : Above (invert (oddReciprocalS p : K[T;T⁻¹])) ((p : ℤ) - 3) := by
    simp only [oddReciprocalS, map_mul, invert_T]
    have he := Above_shift hkernelInv (-((N - 1 : ℕ) : ℤ))
    convert he using 1
    all_goals omega
  have hjne := Finsupp.mem_support_iff.mp hj
  constructor
  · by_contra hlow
    have hc := hOsInv (-j) (by omega)
    rw [invert_apply, neg_neg] at hc
    exact hjne hc
  · by_contra hhigh
    exact hjne (hOs j (by omega))

/-- The whole mixed residual lies in the four-phase band from the literal degree of A. -/
theorem mixedResidual_support (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (P : K[X]) (hP : P.natDegree ≤ 3 * ((p - 1) / 2)) (h : K)
    (j : ℤ) (hj : j ∈ (mixedResidual p P.toLaurent h).coeff.support) :
    -(p : ℤ) - 3 * (((p - 1) / 2 : ℕ) : ℤ) ≤ j ∧ j ≤ 2 * (p : ℤ) - 2 := by
  let N := (p - 1) / 2
  let s : K[X] := WPFiniteWSource.squaredCoordinate
  have hpN : p = 2 * N + 1 := WPFiniteWSource.half_exponent p hp
  have hsdegree : s.natDegree ≤ 1 := by
    dsimp [s, WPFiniteWSource.squaredCoordinate]
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_add_le _ _).trans (by simp))
  have hs : Above (s.toLaurent ^ N) (N : ℤ) := by
    simpa only [Nat.cast_one, mul_one] using Above_pow (Above_toLaurent s 1 hsdegree) N
  have hsInv : Above (invert (s.toLaurent ^ N)) 0 := by
    rw [← map_pow]
    exact Above_invert_toLaurent (s ^ N)
  have hpoly : Above P.toLaurent (3 * (N : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Above_toLaurent P (3 * N) hP
  have hpolyInv := Above_invert_toLaurent P
  have hconst := Above_C (WPFiniteNC122.q p - h : K)
  have hM : Above (mixedEvenSource p P.toLaurent h) (3 * (N : ℤ)) := by
    unfold mixedEvenSource
    exact Above_mono (Above_add (Above_sub hpolyInv hconst)
      (Above_C_mul hpoly (1 / 3))) (by omega)
  have hMInv : Above (invert (mixedEvenSource p P.toLaurent h)) (3 * (N : ℤ)) := by
    have hinv : invert (invert P.toLaurent) = P.toLaurent := involutive_invert _
    unfold mixedEvenSource
    rw [map_add, map_sub, map_mul, hinv]
    simp only [invert_C]
    exact Above_mono (Above_add (Above_sub hpoly hconst)
      (Above_C_mul hpolyInv (1 / 3))) (by omega)
  have h11 : Above (11 : K[T;T⁻¹]) 0 := by
    simpa only [map_ofNat] using Above_C (11 : K)
  have hphi : Above (frobeniusPhi p : K[T;T⁻¹]) 0 := by
    have hmono : Above (4 * T (-(p : ℤ)) : K[T;T⁻¹]) (-(p : ℤ)) := by
      simpa only [map_ofNat] using Above_monomial (4 : K) (-(p : ℤ))
    exact Above_mono (Above_sub hmono h11) (by omega)
  have hphiInv : Above (invert (frobeniusPhi p : K[T;T⁻¹])) (p : ℤ) := by
    have hmono : Above (4 * T (p : ℤ) : K[T;T⁻¹]) (p : ℤ) := by
      simpa only [map_ofNat] using Above_monomial (4 : K) (p : ℤ)
    simp only [frobeniusPhi, map_sub, map_mul, map_ofNat, invert_T, neg_neg]
    exact Above_mono (Above_sub hmono h11) (by omega)
  have hOs : Above (oddReciprocalS p : K[T;T⁻¹]) (N : ℤ) := by
    intro k hk
    by_contra hc
    have hb := (oddReciprocalS_support (K := K) p hp k
      (Finsupp.mem_support_iff.mpr hc)).2
    omega
  have hOsInv : Above (invert (oddReciprocalS p : K[T;T⁻¹])) ((p : ℤ) - 3) := by
    intro k hk
    rw [invert_apply]
    by_contra hc
    have hb := (oddReciprocalS_support (K := K) p hp (-k)
      (Finsupp.mem_support_iff.mpr hc)).1
    omega
  have hR : Above (mixedResidual p P.toLaurent h) (4 * (N : ℤ)) := by
    unfold mixedResidual
    exact Above_mono (Above_add hOs (Above_mul (Above_mul hs hphi) hM)) (by omega)
  have hRInv : Above (invert (mixedResidual p P.toLaurent h))
      ((p : ℤ) + 3 * (N : ℤ)) := by
    simp only [mixedResidual, map_add, map_mul]
    exact Above_mono (Above_add hOsInv (Above_mul (Above_mul hsInv hphiInv) hMInv))
      (by omega)
  have hjne := Finsupp.mem_support_iff.mp hj
  constructor
  · by_contra hlow
    have hc := hRInv (-j) (by omega)
    rw [invert_apply, neg_neg] at hc
    exact hjne hc
  · by_contra hhigh
    exact hjne (hR j (by omega))

end WPFieldAssembly.NativeClosureMixedSource
