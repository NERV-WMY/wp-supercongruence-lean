import WPActualNativeJetRecurrence

open scoped BigOperators Polynomial
open Polynomial WPActualNativeHasse WPActualNativeParameter
  WPActualNativeJetRecurrence WPActualHasseReciprocal

namespace WPActualNativeJetODE

/-- Every coefficient of the actual finite native parameter derivative, reduced. -/
noncomputable def nativeJetField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  ∑ n ∈ Finset.range ((p - 1) / 2 + 1),
    monomial n (parameterJet n (-(p : ℚ) / 6) : ZMod p)

theorem nativeJetField_coeff (p n : ℕ) [Fact p.Prime] : (nativeJetField p).coeff n =
    if n < (p - 1) / 2 + 1 then (parameterJet n (-(p : ℚ) / 6) : ZMod p) else 0 := by
  classical
  simp only [nativeJetField, finsetSum_coeff, coeff_monomial]
  by_cases hn : n < (p - 1) / 2 + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem nativeJetField_origin (p : ℕ) [Fact p.Prime] : (nativeJetField p).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, nativeJetField_coeff, if_pos (by omega), parameterJet_empty]
  norm_num

theorem nativeJetField_degree (p : ℕ) [Fact p.Prime] : (nativeJetField p).natDegree ≤ (p - 1) / 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeJetField_coeff, if_neg (by omega)]

noncomputable def forcedOperator {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  216 * theta (theta P) - X * (216 * theta (theta P) + 216 * theta P + 46 * P)

theorem forcedOperator_coeff_zero {K : Type*} [CommRing K] (P : K[X]) :
    (forcedOperator P).coeff 0 = 0 := by
  simp [forcedOperator, theta_coeff]

theorem forcedOperator_coeff_succ {K : Type*} [CommRing K] (P : K[X]) (n : ℕ) :
    (forcedOperator P).coeff (n + 1) =
      216 * ((n : K) + 1) ^ 2 * P.coeff (n + 1) -
      (216 * (n : K) ^ 2 + 216 * (n : K) + 46) * P.coeff n := by
  simp only [forcedOperator, coeff_sub, coeff_ofNat_mul, coeff_X_mul, coeff_add,
    theta_coeff, Nat.cast_add, Nat.cast_one]
  ring

/-- Full IR10b, with its actual source and the literal N cutoff boundary. -/
theorem actual_nativeJetField_forced_ODE (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    clearedOperator (nativeJetField p) = -forcedOperator (nativeField p (p / 6)) := by
  have hN := actual_half_exponent p (by omega)
  have htail (n : ℕ) (hn : n < p) : (nativeField p (p / 6)).coeff n =
      (WPReview.nativeCoefficient n : ZMod p) := by
    rw [nativeField_coeff]
    split_ifs with hd
    · rfl
    · exact (actual_native_coefficient_field_tail p n (by omega) hn (by omega)).symm
  ext k
  cases k with
  | zero => rw [clearedOperator_coeff_zero, coeff_neg, forcedOperator_coeff_zero, neg_zero]
  | succ n =>
    rw [clearedOperator_coeff_succ, coeff_neg, forcedOperator_coeff_succ,
      nativeJetField_coeff, nativeJetField_coeff]
    by_cases hn : n + 1 < (p - 1) / 2 + 1
    · rw [if_pos hn, if_pos (by omega), htail (n + 1) (by omega), htail n (by omega)]
      convert actual_native_jet_field_recurrence p n (by omega) (by omega) using 1
      ring
    · rw [if_neg hn]
      by_cases hnd : n < (p - 1) / 2 + 1
      · have heq : n = (p - 1) / 2 := by omega
        rw [if_pos hnd, nativeField_coeff, nativeField_coeff,
          if_neg (by omega), if_neg (by omega)]
        have hhalf : (2 * (n : ZMod p) + 1) = 0 := by
          have heqp : 2 * n + 1 = p := by omega
          have hf : (2 * (n : ZMod p) + 1) = (p : ZMod p) := by
            simpa using congrArg (fun m : ℕ => (m : ZMod p)) heqp
          rw [hf, ZMod.natCast_self]
        rw [hhalf]
        ring
      · rw [if_neg hnd, nativeField_coeff, nativeField_coeff,
          if_neg (by omega), if_neg (by omega)]
        ring

end WPActualNativeJetODE
