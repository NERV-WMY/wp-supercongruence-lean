import WPFieldAssembly.ActualEntropyPolynomial
import WPFieldAssembly.ActualFiniteA2
import WPFiniteLVSource

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift
  WPActualRankTwoLegendreField WPFieldAssembly.ActualEntropyPolynomial

namespace WPFieldAssembly.ActualEntropyLogAttachment

set_option maxHeartbeats 1400000

private theorem rationalLogPolynomial_coeff (p n : ℕ) :
    (rationalLogPolynomial p).coeff n =
      if 0 < n ∧ n < p then 1 / (n : ℚ) else 0 := by
  classical
  unfold rationalLogPolynomial
  rw [finsetSum_coeff]
  by_cases hn : n ∈ Finset.Ico 1 p
  · rw [if_pos (by have hh := Finset.mem_Ico.mp hn; omega : 0 < n ∧ n < p),
      Finset.sum_eq_single n]
    · simp only [coeff_C_mul, coeff_X_pow, if_true, mul_one]
    · intro j _ hj
      simp only [coeff_C_mul, coeff_X_pow, if_neg (Ne.symm hj), mul_zero]
    · exact fun h => (h hn).elim
  · rw [if_neg (by
      intro h
      exact hn (Finset.mem_Ico.mpr (by omega)) : ¬ (0 < n ∧ n < p))]
    apply Finset.sum_eq_zero
    intro j hj
    have hnj : n ≠ j := by intro he; subst j; exact hn hj
    simp only [coeff_C_mul, coeff_X_pow, if_neg hnj, mul_zero]

private theorem rationalEvenLog_coeff_even (p j : ℕ) :
    (rationalEvenLog p).coeff (2 * j) =
      if 0 < 2 * j ∧ 2 * j < p then 1 / ((2 * j : ℕ) : ℚ) else 0 := by
  have hs : (-1 : ℚ)^(2 * j) = 1 := by rw [pow_mul]; norm_num
  rw [rationalEvenLog, coeff_C_mul, coeff_add,
    WPActualEvenLogCarry.coeff_comp_neg, hs, rationalLogPolynomial_coeff]
  split_ifs <;> ring

/-- The moving even log is the original retained rational log, in the squared variable. -/
theorem movingEvenQ_eq_actual_contract (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    movingEvenQ p = contract 2 (rationalEvenLog p) := by
  have hpn := WPActualEvenLogCarry.prime_half_identity p (by omega : 7 ≤ p)
  ext j
  rw [movingEvenQ, rankCoefficientPolynomial_coeff,
    coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.mul_comm j 2,
    rationalEvenLog_coeff_even]
  by_cases h0 : j = 0
  · subst j
    simp
  · by_cases hj : j < (p - 1) / 2 + 1
    · simp only [if_pos hj, if_neg h0, if_pos (by omega : 0 < 2 * j ∧ 2 * j < p)]
    · simp only [if_neg hj, if_neg (by omega : ¬ (0 < 2 * j ∧ 2 * j < p))]

theorem movingEvenQ_actual_pullback (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (movingEvenQ p).comp (X^2) = rationalEvenLog p := by
  rw [movingEvenQ_eq_actual_contract p hp, ← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, coeff_contract (by norm_num : (2 : ℕ) ≠ 0),
      Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    have hm : n % 2 = 1 := by
      have ht := Nat.mod_lt n (by norm_num : 0 < (2 : ℕ))
      have hz : n % 2 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hn
      omega
    have ho : Odd n := ⟨n / 2, by have hh := Nat.mod_add_div n 2; omega⟩
    rw [rationalEvenLog, coeff_C_mul, coeff_add,
      WPActualEvenLogCarry.coeff_comp_neg, ho.neg_one_pow]
    ring

theorem movingEvenIntegral_eq_actual_contract (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    movingEvenIntegral p = contract 2 (integralEvenLog p (by omega)) := by
  apply Polynomial.map_injective (integralRationals p).subtype Subtype.val_injective
  rw [movingEvenIntegral_value, map_contract (by norm_num : (2 : ℕ) ≠ 0),
    integralEvenLog_value, movingEvenQ_eq_actual_contract p hp]

theorem movingEvenIntegral_actual_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (movingEvenIntegral p).map (residueHom p) =
      (WPFiniteLVSource.evenSquared p : (ZMod p)[X]) := by
  rw [movingEvenIntegral_eq_actual_contract p hp,
    map_contract (by norm_num : (2 : ℕ) ≠ 0), integralEvenLog_field]
  change contract 2 (WPFiniteKSource.EP p : (ZMod p)[X]) = _
  have he := WPFiniteLVSource.evenSquared_square (K := ZMod p) p hp
  rw [← expand_eq_comp_X_pow] at he
  rw [← he, contract_expand 2 (by norm_num : (2 : ℕ) ≠ 0)]

private theorem H_range (p n : ℕ) [Fact p.Prime] :
    (WPFiniteJSource.H n : ZMod p) =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ZMod p)⁻¹ := by
  induction n with
  | zero => simp [WPFiniteJSource.H]
  | succ n ih =>
    simp only [WPFiniteJSource.H, Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1),
      Finset.sum_range_succ] at ih ⊢
    rw [ih]

private theorem harmonicPrimitive_coeff_even (p j : ℕ) [Fact p.Prime] :
    (ActualFiniteA2.harmonicPrimitive p : (ZMod p)[X]).coeff (2 * j) =
      if 0 < j ∧ j < (p - 1) / 2 + 1 then
        (WPFiniteJSource.H (2 * j - 1) : ZMod p) / ((2 * j : ℕ) : ZMod p) else 0 := by
  classical
  unfold ActualFiniteA2.harmonicPrimitive
  rw [finsetSum_coeff]
  by_cases hj : j ∈ Finset.Ico 1 ((p - 1) / 2 + 1)
  · rw [if_pos (by have hh := Finset.mem_Ico.mp hj; omega :
      0 < j ∧ j < (p - 1) / 2 + 1), Finset.sum_eq_single j]
    · simp only [coeff_C_mul, coeff_X_pow, if_true, mul_one]
    · intro k _ hkj
      simp only [coeff_C_mul, coeff_X_pow, if_neg (by omega : 2 * j ≠ 2 * k), mul_zero]
    · exact fun h => (h hj).elim
  · rw [if_neg (by
      intro h
      exact hj (Finset.mem_Ico.mpr (by omega)) : ¬ (0 < j ∧ j < (p - 1) / 2 + 1))]
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : j ≠ k := by intro he; subst k; exact hj hk
    simp only [coeff_C_mul, coeff_X_pow, if_neg (by omega : 2 * j ≠ 2 * k), mul_zero]

private theorem harmonicPrimitive_coeff_odd (p n : ℕ) [Fact p.Prime] (hn : ¬ 2 ∣ n) :
    (ActualFiniteA2.harmonicPrimitive p : (ZMod p)[X]).coeff n = 0 := by
  unfold ActualFiniteA2.harmonicPrimitive
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  have hnj : n ≠ 2 * j := by
    intro he
    exact hn ⟨j, he⟩
  simp only [coeff_C_mul, coeff_X_pow, if_neg hnj, mul_zero]

/-- Full harmonic carry, after the square pullback and without an endpoint omission. -/
theorem harmonicEvenField_actual_pullback (p : ℕ) [Fact p.Prime] :
    (harmonicEvenField p).comp (X^2) =
      (ActualFiniteA2.harmonicPrimitive p : (ZMod p)[X]) := by
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn]
    obtain ⟨j, rfl⟩ := hn
    rw [show (2*j)/2=j by omega, harmonicEvenField, rankCoefficientPolynomial_coeff,
      harmonicPrimitive_coeff_even]
    by_cases h0 : j = 0
    · subst j
      simp
    · by_cases hj : j < (p - 1) / 2 + 1
      · simp only [if_pos hj, if_neg h0, if_pos (by omega : 0 < j ∧ j < (p - 1) / 2 + 1)]
        rw [H_range]
      · simp only [if_neg hj, if_neg (by omega : ¬ (0 < j ∧ j < (p - 1) / 2 + 1))]
  · rw [if_neg hn, harmonicPrimitive_coeff_odd p n hn]

theorem entropyCarry_actual_Aeven (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (z : ZMod p) :
    (harmonicEvenField p).eval (z^2) = WPFiniteNC122.Aeven p z := by
  have he := congrArg (fun P : (ZMod p)[X] => P.eval z)
    (harmonicEvenField_actual_pullback p)
  simp only [eval_comp, eval_pow, eval_X] at he
  rw [he, ActualFiniteA2.actual_even_dilog_value p hp]

/-- The field endpoint is obtained from the actual rational first difference. -/
theorem actual_entropy_carry_Aeven (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (z : integralRationals p) :
    residueHom p ((entropyCarryIntegral p).eval (z^2)) =
      WPFiniteNC122.Aeven p (residueHom p z) := by
  rw [actual_entropy_evaluation_field, map_pow, entropyCarry_actual_Aeven p hp]

section BaseChange

variable {K : Type*} [Field K]

private theorem harmonicPrimitive_map (p : ℕ) [Fact p.Prime] [CharP K p] :
    (ActualFiniteA2.harmonicPrimitive p : (ZMod p)[X]).map
      (ZMod.castHom (dvd_refl p) K) = (ActualFiniteA2.harmonicPrimitive p : K[X]) := by
  simp only [ActualFiniteA2.harmonicPrimitive, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_div₀,
    WPFiniteJSource.H, map_sum, map_inv₀, map_natCast]

/-- A squared rational point retains both prime classes in any characteristic-p field. -/
theorem entropyCarry_actual_Aeven_baseChange (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ((harmonicEvenField p).map (ZMod.castHom (dvd_refl p) K)).eval (u^2) =
      WPFiniteNC122.Aeven p u := by
  have hm := congrArg (Polynomial.map (ZMod.castHom (dvd_refl p) K))
    (harmonicEvenField_actual_pullback p)
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    harmonicPrimitive_map] at hm
  have he := congrArg (fun P : K[X] => P.eval u) hm
  simp only [eval_comp, eval_pow, eval_X] at he
  rw [he, ActualFiniteA2.actual_even_dilog_value p hp]

/-- The original rational carry is reduced at its actual squared CM point. -/
theorem actual_entropy_carry_square_point (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (s : integralRationals p) (u : K)
    (hu : u^2 = (ZMod.castHom (dvd_refl p) K) (residueHom p s)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p ((entropyCarryIntegral p).eval s)) =
      WPFiniteNC122.Aeven p u := by
  rw [actual_entropy_evaluation_field, ← eval_map_apply, ← hu,
    entropyCarry_actual_Aeven_baseChange p hp]

end BaseChange

end WPFieldAssembly.ActualEntropyLogAttachment

