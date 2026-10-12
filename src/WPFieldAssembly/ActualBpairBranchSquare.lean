import WPFieldAssembly.ActualSB72Finite
import WPFiniteJWeightedResidue
import Mathlib.Algebra.Polynomial.Div

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPFiniteLaurentDifferential
open LaurentPolynomial (T invert T_pow invert_C invert_T T_add T_zero T_apply)

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- A regular differential source forces the whole branch order within the unit band. -/
theorem regular_ode_branch_order (p : ℕ) [Fact p.Prime] [CharP K p]
    (B A S R : K[X]) (n : ℕ) (hn : n < p)
    (hB : B.coeff 0 ≠ 0) (hS : S.coeff 0 = 0)
    (hode : B * S.derivative - A * S = X ^ n * R) : X ^ (n + 1) ∣ S := by
  classical
  apply X_pow_dvd_iff.mpr
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => exact hS
    | succ k =>
      have hsmall (i : ℕ) (hi : i ≤ k) : S.coeff i = 0 :=
        ih i (by omega) (by omega)
      have hBD : (B * S.derivative).coeff k =
          B.coeff 0 * (S.coeff (k + 1) * ((k + 1 : ℕ) : K)) := by
        rw [coeff_mul]
        refine (Finset.sum_eq_single (0, k) ?_ ?_).trans ?_
        · intro t ht hne
          have ht' := Finset.mem_antidiagonal.mp ht
          have ht0 : t.1 ≠ 0 := by
            intro hz
            have he : t = (0, k) := Prod.ext hz (by omega)
            exact hne he
          rw [coeff_derivative, hsmall (t.2 + 1) (by omega), zero_mul, mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_antidiagonal.mpr (by simp))).elim
        · simp only [coeff_derivative, Nat.cast_add, Nat.cast_one]
      have hAS : (A * S).coeff k = 0 := by
        rw [coeff_mul]
        apply Finset.sum_eq_zero
        intro t ht
        have ht' := Finset.mem_antidiagonal.mp ht
        rw [hsmall t.2 (by omega), mul_zero]
      have hR : (X ^ n * R).coeff k = 0 := by
        rw [coeff_X_pow_mul', if_neg (by omega : ¬ n ≤ k)]
      have hc := congrArg (fun P : K[X] => P.coeff k) hode
      rw [coeff_sub, hBD, hAS, hR, sub_zero] at hc
      have hu : ((k + 1 : ℕ) : K) ≠ 0 := WPFiniteField.denominator_ne_zero p (k + 1)
        (Finset.mem_Ico.mpr (by omega))
      exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hB)).resolve_right hu

private theorem finite_reflect_toLaurent (n : ℕ) (P : K[X]) (hP : P.natDegree ≤ n) :
    (P.reflect n).toLaurent = T (n : ℤ) * invert P.toLaurent := by
  refine induction_with_natDegree_le
    (fun P : K[X] => (P.reflect n).toLaurent = T (n : ℤ) * invert P.toLaurent)
    n ?_ ?_ ?_ P hP
  · simp
  · intro j c _ hj
    rw [reflect_C_mul_X_pow, revAt_le hj]
    simp only [map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
      T_pow, invert_C, invert_T, mul_one]
    rw [show ((n - j : ℕ) : ℤ) = (n : ℤ) + -(j : ℤ) by omega, T_add]
    ring
  · intro P Q _ _ hP hQ
    rw [reflect_add, map_add, hP, hQ]
    simp only [map_add, mul_add]

/-- The numerator uses the full plain reciprocal of the retained finite primitive. -/
noncomputable def branchNumerator (p : ℕ) : K[X] :=
  X ^ ((p - 1) / 2 - 1) * Dstar p + (Dstar p).reflect ((p - 1) / 2 - 1)

noncomputable def Dsym (p : ℕ) : K[T;T⁻¹] :=
  (Dstar p).toLaurent + invert (Dstar p).toLaurent

theorem branchNumerator_toLaurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchNumerator p : K[X]).toLaurent =
      T (((p - 1) / 2 - 1 : ℕ) : ℤ) * Dsym p := by
  simp only [branchNumerator, map_add, map_mul, Polynomial.toLaurent_X_pow,
    finite_reflect_toLaurent _ _ (Dstar_degree p hp), Dsym, mul_add]

theorem branchNumerator_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchNumerator p : K[X]).natDegree ≤ 2 * ((p - 1) / 2 - 1) := by
  have hD := Dstar_degree (K := K) p hp
  unfold branchNumerator
  apply (natDegree_add_le _ _).trans
  apply max_le
  · have hX : (X ^ ((p - 1) / 2 - 1) : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by simp
    exact (natDegree_mul_le.trans (Nat.add_le_add hX hD)).trans (by omega)
  · exact natDegree_reflect_le.trans (max_le (by omega) (hD.trans (by omega)))

theorem Dstar_branch_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (Dstar p : K[X]).eval (-1) = 0 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).eval (-1) = 0 := by
    simp [WPFiniteWSource.squaredCoordinate]
  rw [Dstar_literal_sum p hp, eval_mul, eval_C, eval_finsetSum]
  have hz : (∑ j ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
      (C ((1 - (4 : K) ^ j) / (j : K)) *
        WPFiniteWSource.squaredCoordinate ^ j).eval (-1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjpos := (Finset.mem_Ico.mp hj).1
    simp only [eval_mul, eval_C, eval_pow, hs, zero_pow (by omega : j ≠ 0), mul_zero]
  rw [hz, mul_zero]

theorem branchNumerator_branch_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchNumerator p : K[X]).eval (-1) = 0 := by
  let : Invertible (-1 : K) := invertibleOfNonzero (by simp)
  have hr := (eval₂_reflect_eq_zero_iff (RingHom.id K) (-1 : K)
    ((p - 1) / 2 - 1) (Dstar p) (Dstar_degree p hp)).mpr (by
      simpa only [eval₂_id] using Dstar_branch_zero (K := K) p hp)
  simp only [eval₂_id, invOf_eq_inv, inv_neg, inv_one] at hr
  simp only [branchNumerator, eval_add, eval_mul, eval_pow, eval_X,
    Dstar_branch_zero p hp, mul_zero, hr, add_zero]

theorem Dsym_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (WPFiniteZSource.Abar : K[X]).toLaurent * D (Dsym p) =
      LaurentPolynomial.C (5 / 2 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          (T (-(((p - 1) / 2 : ℕ) : ℤ)) - 1) := by
  have he := congrArg (fun P : K[X] => P.toLaurent)
    (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.toLaurent_C] at he
  rw [← D_toLaurent] at he
  have hi := congrArg (fun P : K[T;T⁻¹] => invert P) he
  simp only [map_mul, map_sub, map_one, invert_C,
    WPFiniteZSource.invert_Abar, WPFiniteZSource.invert_squared_power] at hi
  have hi' : (WPFiniteZSource.Abar : K[X]).toLaurent *
      (T (-2) * invert (D (Dstar p).toLaurent)) =
      LaurentPolynomial.C (5 / 2 : K) * (1 -
        T (-(((p - 1) / 2 : ℕ) : ℤ)) *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
    linear_combination hi
  simp only [Dsym, map_add, D_invert]
  linear_combination he - hi'

theorem branchNumerator_cleared_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (WPFiniteZSource.Abar : K[X]) *
      (X * (branchNumerator p).derivative - C (((p - 1) / 2 - 1 : ℕ) : K) *
        branchNumerator p) = C (5 / 2 : K) *
          WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) *
            (1 - X ^ ((p - 1) / 2)) := by
  let n := (p - 1) / 2
  let m := n - 1
  have hm : m + 1 = n := by dsimp [m, n]; omega
  have hT : D (T (m : ℤ) : K[T;T⁻¹]) =
      LaurentPolynomial.C (m : K) * T ((m : ℤ) - 1) := by
    simpa only [map_one, one_mul, Int.cast_natCast] using D_monomial (1 : K) (m : ℤ)
  have hpos : (T 1 * T ((m : ℤ) - 1) : K[T;T⁻¹]) = T (m : ℤ) := by
    rw [← T_add]; congr 1; omega
  have hN : (T 1 * T (m : ℤ) : K[T;T⁻¹]) = T (n : ℤ) := by
    rw [← T_add]; congr 1; omega
  have hcancel : (T (n : ℤ) * T (-(n : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  apply Polynomial.toLaurent_injective
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one]
  rw [← D_toLaurent, branchNumerator_toLaurent p hp, D_mul, hT]
  have hsrc := Dsym_cleared_source (K := K) p hp
  change (WPFiniteZSource.Abar : K[X]).toLaurent *
      (T 1 * (LaurentPolynomial.C (m : K) * T ((m : ℤ) - 1) * Dsym p +
        T (m : ℤ) * D (Dsym p)) - LaurentPolynomial.C (m : K) *
          (T (m : ℤ) * Dsym p)) =
      LaurentPolynomial.C (5 / 2 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ n * (1 - T (n : ℤ))
  calc
    _ = T (n : ℤ) * ((WPFiniteZSource.Abar : K[X]).toLaurent * D (Dsym p)) := by
      linear_combination (WPFiniteZSource.Abar : K[X]).toLaurent *
        LaurentPolynomial.C (m : K) * Dsym p * hpos +
        (WPFiniteZSource.Abar : K[X]).toLaurent * D (Dsym p) * hN
    _ = _ := by
      rw [hsrc]
      linear_combination LaurentPolynomial.C (5 / 2 : K) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ n * hcancel

theorem branchNumerator_divisible (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (X + 1 : K[X]) ^ ((p - 1) / 2 + 1) ∣ branchNumerator p := by
  let n := (p - 1) / 2
  let shift : K[X] := X - 1
  let S : K[X] := (branchNumerator p).comp shift
  let A : K[X] := (WPFiniteZSource.Abar : K[X]).comp shift
  let B : K[X] := A * shift
  let R : K[X] := C (5 / 2 : K) * C ((5 : K)⁻¹ ^ n) * (1 - shift ^ n)
  have hder : S.derivative = (branchNumerator p).derivative.comp shift := by
    simp only [S, shift, derivative_comp, derivative_sub, derivative_X,
      derivative_one, sub_zero, one_mul]
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).comp shift = C (5 : K)⁻¹ * X := by
    simp only [WPFiniteWSource.squaredCoordinate, mul_comp, C_comp, add_comp,
      X_comp, one_comp]
    dsimp only [shift]
    ring
  have hsource : B * S.derivative - (C ((n - 1 : ℕ) : K) * A) * S = X ^ n * R := by
    have h := congrArg (fun P : K[X] => P.comp shift)
      (branchNumerator_cleared_source (K := K) p hp)
    simp only [mul_comp, sub_comp, X_comp, C_comp, pow_comp, one_comp, hs,
      mul_pow, ← map_pow] at h
    change A * (shift * (branchNumerator p).derivative.comp shift -
      C ((n - 1 : ℕ) : K) * S) = C (5 / 2 : K) *
        (C ((5 : K)⁻¹ ^ n) * X ^ n) * (1 - shift ^ n) at h
    rw [← hder] at h
    dsimp only [B, R]
    linear_combination h
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hB : B.coeff 0 ≠ 0 := by
    have he : B.coeff 0 = (25 : K) := by
      simp only [B, A, shift, coeff_zero_eq_eval_zero, eval_mul, eval_comp,
        eval_sub, eval_X, eval_one, zero_sub]
      simp only [WPFiniteZSource.Abar, eval_mul, eval_sub, eval_ofNat, eval_X, eval_one]
      ring
    rw [he, show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero _ h5
  have hS : S.coeff 0 = 0 := by
    simp only [S, coeff_zero_eq_eval_zero, eval_comp, shift,
      eval_sub, eval_X, eval_one, zero_sub, branchNumerator_branch_zero p hp]
  have hdiv := regular_ode_branch_order p B (C ((n - 1 : ℕ) : K) * A) S R n
    (by dsimp [n]; omega) hB hS hsource
  obtain ⟨W, hW⟩ := hdiv
  refine ⟨W.comp (X + 1), ?_⟩
  have he := congrArg (fun P : K[X] => P.comp (X + 1)) hW
  have hshift : shift.comp (X + 1) = X := by
    simp only [shift, sub_comp, X_comp, one_comp]
    ring
  simpa only [S, comp_assoc, hshift, comp_X, mul_comp, pow_comp, X_comp] using he

/-- The quotient is taken by the monic branch divisor before the exact scalar rescaling. -/
noncomputable def branchPolynomial (p : ℕ) : K[X] :=
  C ((5 : K) ^ ((p - 1) / 2 + 1)) *
    ((branchNumerator p) /ₘ (X + 1) ^ ((p - 1) / 2 + 1))

theorem branchPolynomial_factor (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchNumerator p : K[X]) =
      WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2 + 1) * branchPolynomial p := by
  let n := (p - 1) / 2 + 1
  let Q : K[X] := (branchNumerator p) /ₘ (X + 1) ^ n
  obtain ⟨W, hW⟩ := branchNumerator_divisible (K := K) p hp
  have hmonic : ((X + 1 : K[X]) ^ n).Monic := by
    exact (show (X + 1 : K[X]).Monic by simpa only [C_1] using monic_X_add_C (1 : K)).pow n
  have hQ : Q = W := by
    dsimp only [Q, n]
    rw [hW, mul_divByMonic_cancel_left W hmonic]
  have he : (branchNumerator p : K[X]) = (X + 1) ^ n * Q := by rw [hQ]; exact hW
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]) * C (5 : K) = X + 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    calc
      C (5 : K)⁻¹ * (X + 1) * C (5 : K) =
          (C (5 : K)⁻¹ * C (5 : K)) * (X + 1) := by ring
      _ = _ := by rw [← map_mul, inv_mul_cancel₀ h5, map_one, one_mul]
  change branchNumerator p = WPFiniteWSource.squaredCoordinate ^ n * (C ((5 : K) ^ n) * Q)
  rw [map_pow, ← mul_assoc, ← mul_pow, hs]
  exact he

theorem branchPolynomial_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchPolynomial p : K[X]).natDegree ≤ (p - 1) / 2 - 3 := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hsdeg : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree = 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    rw [natDegree_C_mul (inv_ne_zero h5)]
    compute_degree
    exact one_ne_zero
  by_cases hz : (branchPolynomial p : K[X]) = 0
  · rw [hz, natDegree_zero]; omega
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]) ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hsdeg
    omega
  have hdeg := branchNumerator_degree (K := K) p hp
  rw [branchPolynomial_factor p hp, natDegree_mul (pow_ne_zero _ hs) hz,
    natDegree_pow, hsdeg, mul_one] at hdeg
  omega

/-- The entire positive polynomial in the branch square, with the original factor 1/5. -/
noncomputable def branchSquare (p : ℕ) : K[X] :=
  C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate * X ^ 3 * branchPolynomial p ^ 2

theorem branchSquare_origin_order (p : ℕ) : (X : K[X]) ^ 3 ∣ branchSquare p := by
  refine ⟨C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate * branchPolynomial p ^ 2, ?_⟩
  unfold branchSquare
  ring

theorem branchSquare_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (branchSquare p : K[X]).natDegree ≤ p - 3 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have hP := branchPolynomial_degree (K := K) p hp
  have h : (C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate * X ^ 3 *
      branchPolynomial p ^ 2).natDegree ≤
      (C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate * X ^ 3).natDegree +
        (branchPolynomial p ^ 2).natDegree := natDegree_mul_le
  have hX3 : (X ^ 3 : K[X]).natDegree ≤ 3 := by simp
  have hfirst : (C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate * X ^ 3).natDegree ≤ 4 :=
    natDegree_mul_le.trans (Nat.add_le_add ((natDegree_C_mul_le _ _).trans hs) hX3)
  have heven : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  exact (h.trans (Nat.add_le_add hfirst ((natDegree_pow_le).trans
    (Nat.mul_le_mul_left 2 hP)))).trans (by omega)

private theorem squaredCoordinate_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (_hp : 19 ≤ p) : (WPFiniteWSource.squaredCoordinate : K[X]) ^ p =
      C (1 / 5 : K) * (X ^ p + 1) := by
  have h5 : (5 : K) ^ p = 5 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 5
  unfold WPFiniteWSource.squaredCoordinate
  rw [mul_pow, ← map_pow, inv_pow, h5, add_pow_char, one_pow]
  rw [one_div]

theorem Dsym_branch_square (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (Dsym p : K[T;T⁻¹]) ^ 2 =
      (branchSquare p).toLaurent + T (-(p : ℤ)) * (branchSquare p).toLaurent := by
  let n := (p - 1) / 2
  let m := n - 1
  have heven : 2 * n = p - 1 := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    dsimp only [n]
    omega
  have hfactor := congrArg (fun P : K[X] => P.toLaurent)
    (branchPolynomial_factor (K := K) p hp)
  rw [branchNumerator_toLaurent p hp] at hfactor
  simp only [map_mul, map_pow] at hfactor
  have hpow := congrArg (fun P : K[T;T⁻¹] => P ^ 2) hfactor
  rw [mul_pow, T_pow, mul_pow, ← pow_mul] at hpow
  have hsp := congrArg (fun P : K[X] => P.toLaurent)
    (squaredCoordinate_frobenius (K := K) p hp)
  simp only [map_pow, map_mul, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one] at hsp
  have hs : WPFiniteWSource.squaredCoordinate.toLaurent ^ ((n + 1) * 2) =
      LaurentPolynomial.C (1 / 5 : K) * (T (p : ℤ) + 1) *
        WPFiniteWSource.squaredCoordinate.toLaurent := by
    rw [show (n + 1) * 2 = p + 1 by omega, pow_succ, hsp]
  rw [hs] at hpow
  have hshift : (T ((2 : ℤ) * (m : ℤ)) * T (-(p : ℤ)) * T 3 : K[T;T⁻¹]) = 1 := by
    rw [← T_add, ← T_add]
    have hcast : 2 * (m : ℤ) + -(p : ℤ) + 3 = 0 := by dsimp [m]; omega
    rw [hcast, T_zero]
  have hpos : (T ((2 : ℤ) * (m : ℤ)) * T 3 : K[T;T⁻¹]) = T (p : ℤ) := by
    rw [← T_add]; congr 1; dsimp [m]; omega
  have hTne : (T ((2 : ℤ) * (m : ℤ)) : K[T;T⁻¹]) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : K[T;T⁻¹] => P.coeff ((2 : ℤ) * (m : ℤ))) hz
    have he : (1 : K) = 0 := by
      simpa only [T_apply, if_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc
    exact one_ne_zero he
  apply mul_left_cancel₀ hTne
  simp only [branchSquare, map_mul, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one, Nat.cast_ofNat]
  linear_combination hpow -
    LaurentPolynomial.C (1 / 5 : K) * WPFiniteWSource.squaredCoordinate.toLaurent *
      (branchPolynomial p).toLaurent ^ 2 * (hpos + hshift)

theorem branchSquare_coeff_zero (p : ℕ) : (branchSquare p : K[X]).coeff 0 = 0 := by
  obtain ⟨W, hW⟩ := branchSquare_origin_order (K := K) p
  rw [hW, coeff_X_pow_mul', if_neg (by omega : ¬ 3 ≤ 0)]

private theorem negative_shift_trunc_zero (p : ℕ) (P : K[X]) (hP : P.natDegree < p) :
    LaurentPolynomial.trunc (T (-(p : ℤ)) * P.toLaurent) = 0 := by
  ext n
  rw [WPFiniteJWeightedResidue.trunc_coeff, coeff_zero]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) (n : ℤ) P.toLaurent
  simp only [map_one, one_mul] at hs
  rw [hs]
  exact WPFiniteJCarrier.toLaurent_coeff_outside P _ (Or.inr (by omega))

theorem Dsym_square_positive_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : LaurentPolynomial.trunc ((Dsym p : K[T;T⁻¹]) ^ 2) = branchSquare p := by
  rw [Dsym_branch_square p hp, map_add, trunc_toLaurent,
    negative_shift_trunc_zero p _ ((branchSquare_degree p hp).trans_lt (by omega)), add_zero]

/-- The cross-product's literal coefficient at the origin is retained. -/
theorem Dstar_reciprocal_product_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : ((Dstar p).toLaurent * invert (Dstar p).toLaurent).coeff 0 =
      -(Dstar p : K[X]).coeff 0 ^ 2 := by
  have h := congrArg (fun P : K[X] => P.coeff 0)
    (Dsym_square_positive_polynomial (K := K) p hp)
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hsq : (Dsym p : K[T;T⁻¹]) ^ 2 = (Dstar p).toLaurent ^ 2 +
      invert ((Dstar p).toLaurent ^ 2) + LaurentPolynomial.C (2 : K) *
        ((Dstar p).toLaurent * invert (Dstar p).toLaurent) := by
    simp only [Dsym, map_pow]
    change _ = _ + _ + 2 * _
    ring
  rw [hsq, map_add, map_add, ← map_pow (Polynomial.toLaurent), trunc_toLaurent,
    WPFiniteJWeightedResidue.trunc_invert,
    WPFiniteJWeightedResidue.trunc_C_mul, coeff_add, coeff_add, coeff_C_zero,
    coeff_C_mul, WPFiniteJWeightedResidue.trunc_coeff, branchSquare_coeff_zero] at h
  have hD : ((Dstar p : K[X]) ^ 2).coeff 0 = (Dstar p : K[X]).coeff 0 ^ 2 := by
    simp only [pow_two, mul_coeff_zero]
  rw [hD] at h
  apply (mul_left_cancel₀ h2)
  linear_combination h

/-- Removing precisely the origin from the cross-product gives the full positive triangle. -/
theorem Dstar_reciprocal_product_positive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    LaurentPolynomial.trunc ((Dstar p).toLaurent * invert (Dstar p).toLaurent) -
      C (((Dstar p).toLaurent * invert (Dstar p).toLaurent).coeff 0) =
        C (1 / 2 : K) * (branchSquare p - Dstar p ^ 2 + C ((Dstar p : K[X]).coeff 0 ^ 2)) := by
  have h := Dsym_square_positive_polynomial (K := K) p hp
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hsq : (Dsym p : K[T;T⁻¹]) ^ 2 = (Dstar p).toLaurent ^ 2 +
      invert ((Dstar p).toLaurent ^ 2) + LaurentPolynomial.C (2 : K) *
        ((Dstar p).toLaurent * invert (Dstar p).toLaurent) := by
    simp only [Dsym, map_pow]
    change _ = _ + _ + 2 * _
    ring
  rw [hsq, map_add, map_add, ← map_pow (Polynomial.toLaurent), trunc_toLaurent,
    WPFiniteJWeightedResidue.trunc_invert,
    WPFiniteJWeightedResidue.trunc_C_mul] at h
  have hD : ((Dstar p : K[X]) ^ 2).coeff 0 = (Dstar p : K[X]).coeff 0 ^ 2 := by
    simp only [pow_two, mul_coeff_zero]
  rw [hD] at h
  rw [Dstar_reciprocal_product_origin p hp, C_neg]
  have hc : C (2 : K) * C (1 / 2 : K) = (1 : K[X]) := by
    rw [← map_mul, mul_one_div_cancel h2, map_one]
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr h2)
  simp only [C_ofNat] at h hc ⊢
  linear_combination h -
    (branchSquare p - Dstar p ^ 2 + C ((Dstar p : K[X]).coeff 0 ^ 2)) * hc

theorem branchSquare_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (branchSquare p : K[X]).eval (1 / 4) =
      ((Dstar p : K[X]).eval (1 / 4) + (Dstar p : K[X]).eval 4) ^ 2 / 5 ∧
    (branchSquare p : K[X]).eval 4 =
      4 * ((Dstar p : K[X]).eval (1 / 4) + (Dstar p : K[X]).eval 4) ^ 2 / 5 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K) = 4 := rfl
  have ha := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹)
    (Dsym_branch_square (K := K) p hp)
  have hb := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v)
    (Dsym_branch_square (K := K) p hp)
  simp only [Dsym, map_pow, map_add, map_mul, WPFiniteJWeightedResidue.inversion_eval,
    LaurentPolynomial.eval₂_toLaurent, eval₂_id, LaurentPolynomial.eval₂_T_neg_n] at ha hb
  simp only [Units.val_inv_eq_inv_val, hv, inv_inv, inv_pow, h4p] at ha hb
  have hfourinv : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  simp only [one_div] at hfourinv ⊢
  constructor
  · apply (eq_div_iff h5).mpr
    linear_combination -ha
  · apply (eq_div_iff h5).mpr
    linear_combination -4 * hb - (branchSquare p : K[X]).eval 4 * hfourinv

end WPFieldAssembly.ActualBpairContraction
