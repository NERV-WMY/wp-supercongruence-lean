import WPMomentPrecision.SecondLift.LogQuadraticRepresentation

open scoped BigOperators Polynomial
open Polynomial WPActualRankTwoParameter WPActualRankTwoGaussODE
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.TwoNodeSquare
  WPMomentPrecision.LogQuadraticRepresentation

namespace WPMomentPrecision.RationalNodeParity

set_option maxHeartbeats 1600000

/-- The leading indicial factor is read from the whole rational Jacobi ODE. -/
theorem rational_rank_clear_coefficient (t : ℚ) (P : ℚ[X]) (n : ℕ) :
    (rankJacobiClear t P).coeff n =
      36 * ((n : ℚ) + 1) * ((n : ℚ) + 2) * P.coeff (n + 2) -
        (6 * (n : ℚ) + 1 + 6 * t) * (6 * (n : ℚ) + 5 + 6 * t) * P.coeff n := by
  have hform : rankJacobiClear t P = 36 * P.derivative.derivative -
      36 * X ^ 2 * P.derivative.derivative -
      C (72 * (1 + t)) * (X * P.derivative) -
      C ((1 + 6 * t) * (5 + 6 * t)) * P := by
    simp only [rankJacobiClear, map_mul, map_ofNat]
    ring
  rw [hform]
  cases n with
  | zero =>
    simp only [coeff_sub, coeff_ofNat_mul, mul_assoc,
      coeff_X_pow_mul', coeff_X_mul_zero, coeff_C_mul, coeff_derivative]
    norm_num
    ring
  | succ n =>
    cases n with
    | zero =>
      simp only [coeff_sub, coeff_ofNat_mul, mul_assoc,
        coeff_X_pow_mul', coeff_X_mul, coeff_C_mul, coeff_derivative]
      norm_num
      ring
    | succ n =>
      simp only [coeff_sub, coeff_ofNat_mul, mul_assoc,
        coeff_X_pow_mul', coeff_X_mul, coeff_C_mul, coeff_derivative]
      rw [if_pos (by omega)]
      simp only [show n + 1 + 1 - 2 = n by omega,
        Nat.cast_add, Nat.cast_one]
      ring

theorem rational_rank_node_degree_exact (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    (rankJacobiNode p k).natDegree = if k = 1 then p / 6 else p - 1 - p / 6 := by
  let Y := rankJacobiNode p k
  let m := Y.natDegree
  have hY : Y ≠ 0 := by
    intro hz
    have h := rankJacobiNode_endpoint_one p k
    rw [show rankJacobiNode p k = Y from rfl, hz, eval_zero] at h
    exact zero_ne_one h
  have htop : Y.coeff m ≠ 0 := by
    simpa only [m, coeff_natDegree] using (leadingCoeff_ne_zero.mpr hY)
  have h := congrArg (fun P : ℚ[X] => P.coeff m) (actual_rankJacobi_ODE p k (by omega) hk)
  rw [rational_rank_clear_coefficient, coeff_zero,
    coeff_eq_zero_of_natDegree_lt (show Y.natDegree < m + 2 by dsimp [m]; omega),
    mul_zero, zero_sub] at h
  have hf' := (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_right htop
  have hf : (6 * (m : ℚ) + 1 - (k : ℚ) * (p : ℚ)) *
      (6 * (m : ℚ) + 5 - (k : ℚ) * (p : ℚ)) = 0 := by
    linear_combination hf'
  have hroot : 6 * m + 1 = k * p ∨ 6 * m + 5 = k * p := by
    rcases mul_eq_zero.mp hf with hf | hf
    · left
      have he : 6 * (m : ℚ) + 1 = (k : ℚ) * (p : ℚ) := sub_eq_zero.mp hf
      exact_mod_cast he
    · right
      have he : 6 * (m : ℚ) + 5 = (k : ℚ) * (p : ℚ) := sub_eq_zero.mp hf
      exact_mod_cast he
  change m = _
  rcases hk with rfl | rfl
  · rw [if_pos rfl]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with hp1 | hp5 <;> omega
  · rw [if_neg (by norm_num : 5 ≠ 1)]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with hp1 | hp5 <;> omega

/-- A square attached to q fixes the sign of its rational square root by its
nonzero leading coefficient. No endpoint value is assumed nonzero modulo p. -/
theorem rational_square_reflection (P : ℚ[X]) (d : ℕ) (hd : P.coeff d ≠ 0)
    (hsquare : (P ^ 2).comp (-X) = P ^ 2) :
    P.comp (-X) = C ((-1 : ℚ) ^ d) * P := by
  let A := P.comp (-X)
  let B := C ((-1 : ℚ) ^ d) * P
  have hs : ((-1 : ℚ) ^ d) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hsq : A ^ 2 = B ^ 2 := by
    rw [show A ^ 2 = (P ^ 2).comp (-X) by simp only [A, pow_comp], hsquare]
    simp only [B, mul_pow, ← C_pow, hs, C_1, one_mul]
  have hsum : A + B ≠ 0 := by
    intro hz
    have he := congrArg (fun Q : ℚ[X] => Q.coeff d) hz
    simp only [A, B, coeff_add, coeff_zero, coeff_C_mul,
      show (-X : ℚ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff] at he
    have hprod : (2 : ℚ) * ((-1 : ℚ) ^ d) * P.coeff d = 0 := by linear_combination he
    exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero d (by norm_num))) hd) hprod
  have hfactor : (A - B) * (A + B) = 0 := by linear_combination hsq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hsum)

theorem actual_rational_node_reflection (p k : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hk : k = 1 ∨ k = 5) :
    (rankJacobiNode p k).comp (-X) =
      C ((-1 : ℚ) ^ (if k = 1 then p / 6 else p - 1 - p / 6)) * rankJacobiNode p k := by
  have hY : rankJacobiNode p k ≠ 0 := by
    intro hz
    have h := rankJacobiNode_endpoint_one p k
    rw [hz, eval_zero] at h
    exact zero_ne_one h
  have hdegree := rational_rank_node_degree_exact p k hp hk
  have htop : (rankJacobiNode p k).coeff (rankJacobiNode p k).natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.mpr hY)
  rw [hdegree] at htop
  apply rational_square_reflection _ _ htop
  rw [← actual_two_node_Jacobi_square p k hp hk, comp_assoc]
  congr 1
  simp only [sub_comp, one_comp, pow_comp, X_comp, neg_sq]

theorem actual_rational_U_reflection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualU p).comp (-X) = C ((-1 : ℚ) ^ (p / 6)) * actualU p := by
  have hparity : (-1 : ℚ) ^ (p - 1 - p / 6) = (-1 : ℚ) ^ (p / 6) := by
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with hp1 | hp5
    · have he : p - 1 - p / 6 = p / 6 + 2 * (2 * (p / 6)) := by omega
      rw [he, pow_add, pow_mul]
      norm_num
    · have he : p - 1 - p / 6 = p / 6 + 2 * (2 * (p / 6) + 2) := by omega
      rw [he, pow_add, pow_mul]
      norm_num
  rw [actual_U_divided_nodes p (by omega), mul_comp, C_comp, sub_comp,
    actual_rational_node_reflection p 1 hp (Or.inl rfl),
    actual_rational_node_reflection p 5 hp (Or.inr rfl)]
  simp only [if_true, if_neg (by omega : 5 ≠ 1)]
  rw [hparity]
  ring

theorem actual_rational_YU_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankJacobiNode p 1 * actualU p).comp (-X) = rankJacobiNode p 1 * actualU p := by
  rw [mul_comp, actual_rational_node_reflection p 1 hp (Or.inl rfl),
    actual_rational_U_reflection p hp]
  simp only [if_true]
  have hs : ((-1 : ℚ) ^ (p / 6)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  calc
    _ = C (((-1 : ℚ) ^ (p / 6)) ^ 2) * (rankJacobiNode p 1 * actualU p) := by
      simp only [map_pow]; ring
    _ = _ := by rw [hs, C_1, one_mul]

theorem actual_rational_U_square_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualU p ^ 2).comp (-X) = actualU p ^ 2 := by
  rw [pow_comp, actual_rational_U_reflection p hp, mul_pow, ← C_pow]
  have hs : ((-1 : ℚ) ^ (p / 6)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hs, C_1, one_mul]

theorem rational_even_fold_source (d : ℕ) (P : ℚ[X])
    (hdegree : P.natDegree ≤ 2 * d) (hP : P.comp (-X) = P) :
    (evenCoefficientFold d P).comp (X ^ 2) = P := by
  ext n
  rw [← expand_eq_comp_X_pow, coeff_expand (by norm_num : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, evenCoefficientFold_coeff]
    have he : 2 * (n / 2) = n := by have := Nat.div_mul_cancel hn; omega
    by_cases hnd : n / 2 < d + 1
    · rw [if_pos hnd, he]
    · rw [if_neg hnd]
      exact (coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by omega))).symm
  · rw [if_neg hn]
    have hmod : n % 2 ≠ 0 := by intro hz; exact hn (Nat.dvd_of_mod_eq_zero hz)
    have hodd : Odd n := Nat.odd_iff.mpr (by have := Nat.mod_lt n (by omega : 0 < 2); omega)
    have h := congrArg (fun Q : ℚ[X] => Q.coeff n) hP
    rw [show (-X : ℚ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff,
      hodd.neg_one_pow] at h
    have hz : P.coeff n = 0 := by linarith
    exact hz.symm

noncomputable def rationalQFold (d : ℕ) (P : ℚ[X]) : ℚ[X] :=
  (evenCoefficientFold d P).comp (1 - X)

theorem rationalQFold_source (d : ℕ) (P : ℚ[X])
    (hdegree : P.natDegree ≤ 2 * d) (hP : P.comp (-X) = P) :
    (rationalQFold d P).comp (1 - X ^ 2) = P := by
  rw [rationalQFold, comp_assoc,
    show (1 - X : ℚ[X]).comp (1 - X ^ 2) = X ^ 2 by simp]
  exact rational_even_fold_source d P hdegree hP

theorem rationalQFold_degree (d : ℕ) (P : ℚ[X]) :
    (rationalQFold d P).natDegree ≤ d := by
  have hq : (1 - X : ℚ[X]).natDegree ≤ 1 := by compute_degree
  exact natDegree_comp_le.trans ((Nat.mul_le_mul (evenCoefficientFold_degree _ _) hq).trans
    (by omega))

end WPMomentPrecision.RationalNodeParity
