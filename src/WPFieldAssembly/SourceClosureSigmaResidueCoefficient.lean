import WPFiniteLaurentDifferential

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.SourceClosureSigmaResidueCoefficient

set_option maxHeartbeats 1500000

variable {K : Type*} [Field K]

noncomputable def reciprocalJet (p : ℕ) (c : K) : K[X] :=
  ∑ j ∈ Finset.range p, X ^ j * Polynomial.C (c ^ (p - 1 - j))

theorem reciprocalJet_source (p : ℕ) (c : K) :
    (X - Polynomial.C c) * reciprocalJet p c =
      (X : K[X]) ^ p - Polynomial.C (c ^ p) := by
  simp only [reciprocalJet, _root_.map_pow]
  exact (Commute.all (X : K[X]) (Polynomial.C c)).mul_geom_sum₂ p

theorem reciprocalJet_degree (p : ℕ) (c : K) :
    (reciprocalJet p c).natDegree ≤ p - 1 := by
  unfold reciprocalJet
  apply natDegree_sum_le_of_forall_le
  intro j hj
  rw [mul_comm]
  exact (natDegree_C_mul_le _ _).trans (by
    rw [natDegree_X_pow]
    have := Finset.mem_range.mp hj
    omega)

theorem reciprocalJet_coeff (p : ℕ) (c : K) (j : ℕ) (hj : j < p) :
    (reciprocalJet p c).coeff j = c ^ (p - 1 - j) := by
  rw [reciprocalJet, finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [coeff_mul_C, coeff_X_pow, if_pos rfl, one_mul]
  · intro k _ hkj
    rw [coeff_mul_C, coeff_X_pow, if_neg (Ne.symm hkj), zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hj))

theorem reciprocalJet_product_coeff (p : ℕ) (hp : 0 < p) (c : K) (W : K[X])
    (hW : W.natDegree < p) :
    (reciprocalJet p c * W).coeff (p - 1) = W.eval c := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    show (p - 1).succ = p by omega, Polynomial.eval_eq_sum_range' hW]
  apply Finset.sum_congr rfl
  intro j hj
  have hjp := Finset.mem_range.mp hj
  rw [reciprocalJet_coeff p c (p - 1 - j) (by omega),
    show p - 1 - (p - 1 - j) = j by omega]

theorem shifted_reciprocalJet_product_coeff (p : ℕ) (hp : 0 < p)
    (a b : K) (W : K[X]) (hW : W.natDegree < p) :
    ((X ^ p - Polynomial.C a) * reciprocalJet p b * W).coeff (2 * p - 1) = W.eval b := by
  have hdeg : (reciprocalJet p b * W).natDegree < 2 * p - 1 := by
    exact (natDegree_mul_le (p := reciprocalJet p b) (q := W)).trans_lt (by
      have := reciprocalJet_degree p b
      omega)
  have hn : 2 * p - 1 = (p - 1) + p := by omega
  rw [sub_mul, sub_mul, coeff_sub, mul_assoc, mul_assoc, coeff_C_mul,
    coeff_eq_zero_of_natDegree_lt hdeg, mul_zero, sub_zero, hn,
    coeff_X_pow_mul, reciprocalJet_product_coeff p hp b W hW]

/-- The whole high coefficient is the sum of its two original rational endpoint evaluations. -/
theorem quadratic_log_high_coeff (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 0 < p) (a b lam : K) (hlam : lam ≠ 0) (hlamp : lam ^ p = lam)
    (hap : a ^ p = a) (hbp : b ^ p = b) (W : K[X]) (hW : W.natDegree < p) :
    (((Polynomial.C lam * (X - Polynomial.C a) * (X - Polynomial.C b)) ^ (p - 1)) *
      (Polynomial.C lam * (X - Polynomial.C a) * (X - Polynomial.C b)).derivative * W).coeff
        (2 * p - 1) = lam * (W.eval a + W.eval b) := by
  let A : K[X] := Polynomial.C lam * (X - Polynomial.C a) * (X - Polynomial.C b)
  have hA : A ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr hlam)
      (X_sub_C_ne_zero a)) (X_sub_C_ne_zero b)
  have hAp : A ^ p = Polynomial.C lam * (X ^ p - Polynomial.C a) *
      (X ^ p - Polynomial.C b) := by
    simp only [A, mul_pow, sub_pow_char, ← _root_.map_pow, hlamp, hap, hbp]
  have hAD : A.derivative = Polynomial.C lam *
      (2 * X - Polynomial.C a - Polynomial.C b) := by
    simp only [A, derivative_mul, derivative_C, derivative_sub, derivative_X,
      zero_mul, sub_zero, mul_one]
    ring
  have hquad : A ^ (p - 1) * A.derivative = Polynomial.C lam *
      ((X ^ p - Polynomial.C a) * reciprocalJet p b +
        (X ^ p - Polynomial.C b) * reciprocalJet p a) := by
    apply mul_left_cancel₀ hA
    have hpow : A * A ^ (p - 1) = A ^ p := by
      rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
    have ha := reciprocalJet_source p a
    have hb := reciprocalJet_source p b
    rw [hap] at ha
    rw [hbp] at hb
    calc
      _ = A ^ p * A.derivative := by rw [← mul_assoc, hpow]
      _ = _ := by
        rw [hAp, hAD]
        dsimp only [A]
        linear_combination
          -Polynomial.C lam ^ 2 * (X - Polynomial.C a) *
            (X ^ p - Polynomial.C a) * hb -
          Polynomial.C lam ^ 2 * (X - Polynomial.C b) *
            (X ^ p - Polynomial.C b) * ha
  change (A ^ (p - 1) * A.derivative * W).coeff (2 * p - 1) = _
  rw [hquad, mul_assoc, add_mul, coeff_C_mul, coeff_add,
    shifted_reciprocalJet_product_coeff p hp a b W hW,
    shifted_reciprocalJet_product_coeff p hp b a W hW]
  ring

end WPFieldAssembly.SourceClosureSigmaResidueCoefficient
