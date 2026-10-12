import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1400000

/-- These are the actual two branch powers in both prime classes. -/
theorem lowH_trace_branch_powers (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 : K) ^ ((p - 1) / 2) = 1 ∧ (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have he : (2 : K) ^ p = 2 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 2
  rw [← hN, pow_succ, pow_mul, show (2 : K) ^ 2 = 4 by ring] at he
  have h4 : (4 : K) ^ ((p - 1) / 2) = 1 := by
    apply mul_right_cancel₀ h2
    simpa only [one_mul] using he
  exact ⟨h4, by rw [div_pow, one_pow, h4, one_div_one]⟩

theorem lowH_trace_branch_previous_powers (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (4 : K) ^ ((p - 1) / 2 - 1) = 1 / 4 ∧
      (1 / 4 : K) ^ ((p - 1) / 2 - 1) = 4 := by
  have he := lowH_trace_branch_powers (K := K) p hp
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := div_ne_zero one_ne_zero h4
  have hN : ((p - 1) / 2 - 1) + 1 = (p - 1) / 2 := by omega
  have hb := he.1
  have ha' := he.2
  rw [← hN, pow_succ] at hb ha'
  constructor
  · apply (eq_div_iff h4).mpr
    exact hb
  · apply mul_right_cancel₀ ha
    rw [ha', mul_one_div_cancel h4]

/-- The finite coefficient rule retains every negative exponent and each origin term. -/
theorem lowH_trace_origin_monomial (c : K) (n : ℤ) :
    originPole (LaurentPolynomial.C c * T n) =
      if n < 0 then c * ((1 / 4 : K) ^ (-n).toNat - (4 : K) ^ (-n).toNat) / 15 else 0 := by
  rw [originPole_trunc_inverse, map_mul, invert_C, invert_T, trunc_C_mul_T]
  by_cases hn : n < 0
  · rw [if_pos (by omega : 0 ≤ -n), if_pos hn, eval_monomial, eval_monomial]
    ring
  · rw [if_neg hn]
    by_cases hz : n = 0
    · subst n
      simp
    · rw [if_neg (by omega : ¬0 ≤ -n)]
      simp

/-- This is the whole original trace numerator, with both positive and reciprocal phases. -/
noncomputable def lowHOriginalTraceNumerator (p : ℕ) : K[T;T⁻¹] :=
  (T (p : ℤ) + 1) * (4 * T 1 - 11) * (T (-(((p - 1) / 2 : ℕ) : ℤ)) - 1)

theorem lowHOriginalTraceNumerator_full_bands (p : ℕ) :
    lowHOriginalTraceNumerator (K := K) p =
      LaurentPolynomial.C (4 : K) * T ((p : ℤ) + 1 - (((p - 1) / 2 : ℕ) : ℤ)) -
      LaurentPolynomial.C (11 : K) * T ((p : ℤ) - (((p - 1) / 2 : ℕ) : ℤ)) -
      LaurentPolynomial.C (4 : K) * T ((p : ℤ) + 1) + LaurentPolynomial.C (11 : K) * T (p : ℤ) +
      LaurentPolynomial.C (4 : K) * T (1 - (((p - 1) / 2 : ℕ) : ℤ)) -
      LaurentPolynomial.C (11 : K) * T (-(((p - 1) / 2 : ℕ) : ℤ)) -
      LaurentPolynomial.C (4 : K) * T 1 + LaurentPolynomial.C (11 : K) := by
  simp only [lowHOriginalTraceNumerator, map_ofNat, mul_sub, add_mul, sub_mul,
    one_mul, mul_one]
  simp only [show (p : ℤ) + 1 - (((p - 1) / 2 : ℕ) : ℤ) =
      (p : ℤ) + 1 + -(((p - 1) / 2 : ℕ) : ℤ) by ring,
    show (p : ℤ) - (((p - 1) / 2 : ℕ) : ℤ) = (p : ℤ) + -(((p - 1) / 2 : ℕ) : ℤ) by ring,
    show (1 : ℤ) - (((p - 1) / 2 : ℕ) : ℤ) = 1 + -(((p - 1) / 2 : ℕ) : ℤ) by ring,
    T_add]
  ring

/-- The literal trace value is obtained from the actual numerator and branch powers. -/
theorem lowH_original_trace_functional (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole (lowHOriginalTraceNumerator (K := K) p) = 1 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have he := lowH_trace_branch_powers (K := K) p hp
  have hpw := lowH_trace_branch_previous_powers (K := K) p hp
  rw [lowHOriginalTraceNumerator_full_bands]
  have hC : originPole (LaurentPolynomial.C (11 : K)) = 0 := by
    simpa only [Polynomial.toLaurent_C] using originPole_polynomial (Polynomial.C (11 : K))
  simp only [originPole_add, originPole_sub, lowH_trace_origin_monomial, hC,
    if_neg (by omega : ¬((p : ℤ) + 1 - (((p - 1) / 2 : ℕ) : ℤ) < 0)),
    if_neg (by omega : ¬((p : ℤ) - (((p - 1) / 2 : ℕ) : ℤ) < 0)),
    if_neg (by omega : ¬((p : ℤ) + 1 < 0)),
    if_neg (by omega : ¬((p : ℤ) < 0)),
    if_neg (by omega : ¬((1 : ℤ) < 0)),
    if_pos (by omega : (1 : ℤ) - (((p - 1) / 2 : ℕ) : ℤ) < 0),
    if_pos (by omega : -(((p - 1) / 2 : ℕ) : ℤ) < 0),
    show (-(1 - (((p - 1) / 2 : ℕ) : ℤ))).toNat = (p - 1) / 2 - 1 by omega,
    neg_neg, Int.toNat_natCast, he.1, he.2, hpw.1, hpw.2]
  field_simp [h4, h15]
  ring

end WPFieldAssembly.ActualBpairContraction
