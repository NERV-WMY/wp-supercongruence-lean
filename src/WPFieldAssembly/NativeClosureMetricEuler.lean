import WPFieldAssembly.ActualBpairMetric

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 2200000

/-- The first shifted pole retains the true polynomial origin. -/
theorem metric_first_shift_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (m : K[X]) :
    originPole (T (-1) * m.toLaurent) = -m.coeff 0 / 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hunit : (T (-1) * T 1 : K[T;T⁻¹]) = 1 := by
    rw [← T_add]; norm_num
  have hd := congrArg (fun P : K[X] => P.toLaurent) (X_mul_divX_add m)
  simp only [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C] at hd
  have hs : T (-1) * m.toLaurent = m.divX.toLaurent +
      LaurentPolynomial.C (m.coeff 0) * T (-1) := by
    linear_combination -T (-1) * hd + m.divX.toLaurent * hunit
  have h1 := originPole_shifted_polynomial p 1 hp (1 : K[X]) (by simp)
  simp only [map_one, mul_one, pow_one, eval_one,
    show -((1 : ℕ) : ℤ) = -1 from rfl] at h1
  rw [hs, originPole_add, originPole_polynomial, zero_add, originPole_C_mul, h1]
  field_simp [h4, h15]
  ring

/-- The full positive cleared derivative after m*s^N=(x^p+1)*g/5. -/
noncomputable def metricDuCleared (p : ℕ) (m g : K[X]) : K[T;T⁻¹] :=
  LaurentPolynomial.C (3 / 2 : K) *
    ((m * (4 * X - 11) + Polynomial.C (11 / 5 : K) * g).toLaurent +
      LaurentPolynomial.C (7 / 5 : K) * T (p : ℤ) * g.toLaurent -
      LaurentPolynomial.C (4 / 5 : K) * T (2 * (p : ℤ)) * g.toLaurent)

/-- Both distinct Frobenius and ordinary linear factors remain in the raw source. -/
theorem metricDuCleared_raw (p : ℕ) (m g : K[X]) :
    metricDuCleared p m g = LaurentPolynomial.C (3 / 2 : K) *
      (m.toLaurent * (4 * T 1 - 11) - LaurentPolynomial.C (1 / 5 : K) *
        (T (p : ℤ) + 1) * g.toLaurent * (4 * T (p : ℤ) - 11)) := by
  have ht : (T (p : ℤ) * T (p : ℤ) : K[T;T⁻¹]) = T (2 * (p : ℤ)) := by
    rw [← T_add]; congr 1; omega
  simp only [metricDuCleared, map_add, map_mul, map_sub, map_ofNat,
    Polynomial.toLaurent_X, Polynomial.toLaurent_C]
  have h7 : (7 / 5 : K) = 7 * (1 / 5) := by ring
  have h11 : (11 / 5 : K) = 11 * (1 / 5) := by ring
  have h4 : (4 / 5 : K) = 4 * (1 / 5) := by ring
  rw [h7, h11, h4]
  simp only [map_mul, map_ofNat]
  linear_combination LaurentPolynomial.C (3 / 2 : K) *
    LaurentPolynomial.C (1 / 5 : K) * 4 * g.toLaurent * ht

/-- The complete high positive coefficient is fixed by the two genuine ends. -/
theorem metric_du_high_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (m g : K[X]) (hm : m.natDegree ≤ p - 2)
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    originPole (T (-(p : ℤ)) * metricDuCleared p m g) =
      (24 * m.eval (1 / 4) + 9 * m.eval 4) / 50 := by
  let P : K[X] := m * (4 * X - 11) + Polynomial.C (11 / 5 : K) * g
  have hP : P.natDegree ≤ p := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le_of_le hm
        (show (4 * X - 11 : K[X]).natDegree ≤ 1 by compute_degree)).trans (by omega)
    · exact (natDegree_C_mul_le _ _).trans (hg.trans (by omega))
  have ht0 : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have ht1 : (T (-(p : ℤ)) * T (2 * (p : ℤ)) : K[T;T⁻¹]) = T (p : ℤ) := by
    rw [← T_add]; congr 1; omega
  have hs : T (-(p : ℤ)) * metricDuCleared p m g =
      LaurentPolynomial.C (3 / 2 : K) *
        (T (-(p : ℤ)) * P.toLaurent + (Polynomial.C (7 / 5 : K) * g).toLaurent -
          (Polynomial.C (4 / 5 : K) * X ^ p * g).toLaurent) := by
    simp only [metricDuCleared, P, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X_pow]
    linear_combination LaurentPolynomial.C (3 / 2 : K) *
      LaurentPolynomial.C (7 / 5 : K) * g.toLaurent * ht0 -
      LaurentPolynomial.C (3 / 2 : K) *
      LaurentPolynomial.C (4 / 5 : K) * g.toLaurent * ht1
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  rw [hs, originPole_C_mul, originPole_sub, originPole_add,
    originPole_polynomial, originPole_polynomial, add_zero, sub_zero,
    originPole_shifted_polynomial p p hp P hP, hap, h4p]
  simp only [P, eval_add, eval_mul, eval_C, eval_sub, eval_ofNat, eval_X, ha, hb]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by norm_num]; exact mul_ne_zero h3 h5
  have h50 : (50 : K) ≠ 0 := by
    rw [show (50 : K) = 2 * 5 ^ 2 by norm_num]; exact mul_ne_zero h2 (pow_ne_zero 2 h5)
  field_simp [h2, h4, h5, h15, h50]
  ring

/-- The entire reciprocal derivative keeps its two negative half bands. -/
noncomputable def metricDvCleared (p : ℕ) (m g : K[X]) : K[T;T⁻¹] :=
  LaurentPolynomial.C (-3 / 2 : K) *
      (4 * T (-1) * m.toLaurent - 11 * m.toLaurent) +
    LaurentPolynomial.C (3 / 10 : K) *
      (-7 * T (-(((p - 1) / 2 : ℕ) : ℤ)) * g.toLaurent +
        4 * T (-((((p - 1) / 2 + p : ℕ)) : ℤ)) * g.toLaurent -
        11 * T (((p - (p - 1) / 2 : ℕ)) : ℤ) * g.toLaurent)

/-- The first reciprocal residue retains m(0) until the complete collector cancels it. -/
theorem metric_dv_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (m g : K[X])
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    originPole (metricDvCleared p m g) =
      3 * m.coeff 0 / 2 - 18 * m.eval (1 / 4) / 25 - 3 * m.eval 4 / 25 := by
  let N := (p - 1) / 2
  have hN := originPole_shifted_polynomial p N hp g (hg.trans (by dsimp [N]; omega))
  have hNp := originPole_shifted_polynomial p (N + p) hp g
    (hg.trans (by dsimp [N]; omega))
  have h4N : (4 : K) ^ N = 1 := WPFiniteWSource.four_half_power p hp
  have haN : (1 / 4 : K) ^ N = 1 := by rw [div_pow, one_pow, h4N, div_one]
  have h4p : (4 : K) ^ p = 4 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  rw [haN, h4N, one_mul, one_mul, ha, hb] at hN
  rw [pow_add, pow_add, haN, h4N, hap, h4p, one_mul, one_mul, ha, hb] at hNp
  have hpos : originPole (T ((p - N : ℕ) : ℤ) * g.toLaurent) = 0 := by
    rw [← Polynomial.toLaurent_X_pow, ← map_mul, originPole_polynomial]
  have hs : metricDvCleared p m g =
      LaurentPolynomial.C (-3 / 2 : K) *
        (LaurentPolynomial.C (4 : K) * (T (-1) * m.toLaurent) -
          LaurentPolynomial.C (11 : K) * m.toLaurent) +
      LaurentPolynomial.C (3 / 10 : K) *
        (LaurentPolynomial.C (-7 : K) * (T (-(N : ℤ)) * g.toLaurent) +
          LaurentPolynomial.C (4 : K) * (T (-((N + p : ℕ) : ℤ)) * g.toLaurent) -
          LaurentPolynomial.C (11 : K) * (T ((p - N : ℕ) : ℤ) * g.toLaurent)) := by
    simp only [metricDvCleared, N, map_neg, map_ofNat]
    ring
  rw [hs, originPole_add, originPole_C_mul, originPole_sub,
    originPole_C_mul, originPole_C_mul, originPole_polynomial, mul_zero, sub_zero,
    metric_first_shift_origin p hp, originPole_C_mul, originPole_sub, originPole_add,
    originPole_C_mul, originPole_C_mul, originPole_C_mul, hN, hNp, hpos,
    mul_zero, sub_zero]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by norm_num]; exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by norm_num]; exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by norm_num]; exact pow_ne_zero 2 h5
  field_simp [h2, h4, h10, h15, h25]
  ring

end WPFieldAssembly.ActualBpairContraction
