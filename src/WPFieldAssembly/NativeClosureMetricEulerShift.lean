import WPFieldAssembly.NativeClosureMetricEuler

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualSimplePoleResidue
  WPFiniteLaurentDifferential

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 2200000

/-- The complete positive numerator is polynomial, including its full 2p phase. -/
theorem metricDuCleared_as_polynomial (p : ℕ) (m g : K[X]) :
    metricDuCleared p m g =
      (Polynomial.C (3 / 2 : K) *
        (m * (4 * X - 11) + Polynomial.C (11 / 5 : K) * g +
          Polynomial.C (7 / 5 : K) * X ^ p * g -
            Polynomial.C (4 / 5 : K) * X ^ (2 * p) * g)).toLaurent := by
  simp only [metricDuCleared, map_mul, map_add, map_sub, map_ofNat,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X, Polynomial.toLaurent_X_pow,
    Nat.cast_mul, Nat.cast_ofNat]

/-- The whole positive Euler source keeps all phases until the polynomial residues vanish. -/
theorem metric_du_positive_euler_origin (p : ℕ) (m g : K[X]) :
    -originPole ((LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
        (4 * T (p : ℤ) - 11) + LaurentPolynomial.C (1 / 9 : K) *
          (4 * T (-(p : ℤ)) - 11)) * metricDuCleared p m g) =
      -(4 / 9 : K) * originPole (T (-(p : ℤ)) * metricDuCleared p m g) := by
  have hz (k : ℕ) : originPole (T (k : ℤ) * metricDuCleared p m g) = 0 := by
    rw [metricDuCleared_as_polynomial, ← Polynomial.toLaurent_X_pow,
      ← map_mul, originPole_polynomial]
  have h0 := hz 0
  simp only [Nat.cast_zero, T_zero, one_mul] at h0
  have h1 := hz p
  have h2 := hz (2 * p)
  rw [Nat.cast_mul, Nat.cast_ofNat] at h2
  have ht : (T (p : ℤ) * T (p : ℤ) : K[T;T⁻¹]) = T (2 * (p : ℤ)) := by
    rw [← T_add]; congr 1; omega
  have hs : (LaurentPolynomial.C (5 / 24 : K) * T (p : ℤ) *
        (4 * T (p : ℤ) - 11) + LaurentPolynomial.C (1 / 9 : K) *
          (4 * T (-(p : ℤ)) - 11)) * metricDuCleared p m g =
      LaurentPolynomial.C (5 / 24 : K) *
        (LaurentPolynomial.C (4 : K) * (T (2 * (p : ℤ)) * metricDuCleared p m g) -
          LaurentPolynomial.C (11 : K) * (T (p : ℤ) * metricDuCleared p m g)) +
      LaurentPolynomial.C (1 / 9 : K) *
        (LaurentPolynomial.C (4 : K) * (T (-(p : ℤ)) * metricDuCleared p m g) -
          LaurentPolynomial.C (11 : K) * metricDuCleared p m g) := by
    simp only [map_ofNat]
    linear_combination LaurentPolynomial.C (5 / 24 : K) * 4 * metricDuCleared p m g * ht
  rw [hs, originPole_add, originPole_C_mul, originPole_sub, originPole_C_mul,
    originPole_C_mul, h2, h1, mul_zero, mul_zero, sub_self, mul_zero, zero_add,
    originPole_C_mul, originPole_sub, originPole_C_mul, originPole_C_mul, h0,
    mul_zero, sub_zero]
  ring

/-- The reciprocal cleared source retains both distinct Frobenius half bands. -/
theorem metricDvCleared_raw (p : ℕ) (m g : K[X]) :
    metricDvCleared p m g = LaurentPolynomial.C (-3 / 2 : K) *
      (m.toLaurent * (4 * T (-1) - 11) - LaurentPolynomial.C (1 / 5 : K) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) * (T (p : ℤ) + 1) * g.toLaurent *
          (4 * T (-(p : ℤ)) - 11)) := by
  let N := (p - 1) / 2
  have ht0 : (T (-(N : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) =
      T (-((N + p : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; omega
  have ht1 : (T (-(N : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) =
      T ((p - N : ℕ) : ℤ) := by
    rw [← T_add]; congr 1; dsimp [N]; omega
  have ht2 : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hq : (3 / 10 : K) = (3 / 2) * (1 / 5) := by
    rw [div_mul_div_comm, mul_one]
    congr 1
    norm_num
  simp only [metricDvCleared, hq, map_mul]
  change _ = LaurentPolynomial.C (-3 / 2 : K) *
    (m.toLaurent * (4 * T (-1) - 11) - LaurentPolynomial.C (1 / 5 : K) *
      T (-(N : ℤ)) * (T (p : ℤ) + 1) * g.toLaurent * (4 * T (-(p : ℤ)) - 11))
  simp only [neg_div, map_neg]
  linear_combination
    -LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) * g.toLaurent * 4 * ht0 +
      LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) * g.toLaurent * 11 * ht1 -
      LaurentPolynomial.C (3 / 2 : K) * LaurentPolynomial.C (1 / 5 : K) *
        g.toLaurent * 4 * T (-(N : ℤ)) * ht2

/-- The true origin logarithm loses its high coefficient only by the whole degree bound. -/
theorem metric_logarithmic_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2) :
    (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) *
      T (-1) * m.toLaurent).coeff (-1) = (11 / 6 : ZMod p) * m.coeff 0 := by
  have ht : (T (-(p : ℤ)) * T (-1) : (ZMod p)[T;T⁻¹]) =
      T (-((p + 1 : ℕ) : ℤ)) := by
    rw [← T_add]; congr 1; omega
  have h4 : (-4 / 6 : ZMod p) = -4 * (1 / 6) := by ring
  have h11 : (11 / 6 : ZMod p) = 11 * (1 / 6) := by ring
  have hs : -LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) *
      T (-1) * m.toLaurent =
        LaurentPolynomial.C (-4 / 6 : ZMod p) * T (-((p + 1 : ℕ) : ℤ)) * m.toLaurent +
          LaurentPolynomial.C (11 / 6 : ZMod p) * T (-1) * m.toLaurent := by
    rw [h4, h11]
    simp only [map_mul, map_neg, map_ofNat]
    linear_combination -4 * LaurentPolynomial.C (1 / 6 : ZMod p) * m.toLaurent * ht
  have hp0 : m.toLaurent.coeff (p : ℤ) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hh := WPFiniteJCarrier.shifted_coeff (-4 / 6 : ZMod p)
    (-((p + 1 : ℕ) : ℤ)) (-1) m.toLaurent
  rw [show (-1 : ℤ) - -((p + 1 : ℕ) : ℤ) = p by omega, hp0, mul_zero] at hh
  have hzero := WPFiniteJCarrier.shifted_coeff (11 / 6 : ZMod p) (-1) (-1) m.toLaurent
  rw [sub_self, ← show ((0 : ℕ) : ℤ) = 0 from rfl,
    WPFiniteJCarrier.toLaurent_coeff_nat] at hzero
  rw [hs, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hh, hzero, zero_add]

/-- After the whole p-shift, precisely the second negative half band contributes. -/
theorem metric_dv_frobenius_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (m g : K[X])
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    originPole (T (p : ℤ) * metricDvCleared p m g) =
      (2 / 25 : K) * (m.eval 4 - 4 * m.eval (1 / 4)) := by
  let N := (p - 1) / 2
  have ht1 : (T (p : ℤ) * T (-1) : K[T;T⁻¹]) = T ((p - 1 : ℕ) : ℤ) := by
    rw [← T_add]; congr 1; omega
  have htN : (T (p : ℤ) * T (-(N : ℤ)) : K[T;T⁻¹]) =
      T ((p - N : ℕ) : ℤ) := by
    rw [← T_add]; congr 1; dsimp [N]; omega
  have htNp : (T (p : ℤ) * T (-((N + p : ℕ) : ℤ)) : K[T;T⁻¹]) = T (-(N : ℤ)) := by
    rw [← T_add]; congr 1; omega
  have htpN : (T (p : ℤ) * T ((p - N : ℕ) : ℤ) : K[T;T⁻¹]) =
      T ((2 * p - N : ℕ) : ℤ) := by
    rw [← T_add]; congr 1; dsimp [N]; omega
  have hs : T (p : ℤ) * metricDvCleared p m g =
      LaurentPolynomial.C (-3 / 2 : K) *
        ((Polynomial.C (4 : K) * X ^ (p - 1) * m).toLaurent -
          (Polynomial.C (11 : K) * X ^ p * m).toLaurent) +
      LaurentPolynomial.C (3 / 10 : K) *
        (-(Polynomial.C (7 : K) * X ^ (p - N) * g).toLaurent +
          LaurentPolynomial.C (4 : K) * (T (-(N : ℤ)) * g.toLaurent) -
          (Polynomial.C (11 : K) * X ^ (2 * p - N) * g).toLaurent) := by
    simp only [metricDvCleared, N, map_mul,
      Polynomial.toLaurent_X_pow, map_ofNat]
    linear_combination
      LaurentPolynomial.C (-3 / 2 : K) * 4 * m.toLaurent * ht1 -
      LaurentPolynomial.C (3 / 10 : K) * 7 * g.toLaurent * htN +
      LaurentPolynomial.C (3 / 10 : K) * 4 * g.toLaurent * htNp -
      LaurentPolynomial.C (3 / 10 : K) * 11 * g.toLaurent * htpN
  have hN := originPole_shifted_polynomial p N hp g (hg.trans (by dsimp [N]; omega))
  have h4N : (4 : K) ^ N = 1 := WPFiniteWSource.four_half_power p hp
  have haN : (1 / 4 : K) ^ N = 1 := by rw [div_pow, one_pow, h4N, div_one]
  rw [haN, h4N, one_mul, one_mul, ha, hb] at hN
  have hzero : originPole (-(Polynomial.C (7 : K) * X ^ (p - N) * g).toLaurent) = 0 := by
    rw [← map_neg, originPole_polynomial]
  rw [hs, originPole_add, originPole_C_mul, originPole_sub,
    originPole_polynomial, originPole_polynomial, sub_self, mul_zero, zero_add,
    originPole_C_mul, originPole_sub, originPole_add, hzero, zero_add,
    originPole_C_mul, hN, originPole_polynomial, sub_zero]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by norm_num]; exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by norm_num]; exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by norm_num]; exact pow_ne_zero 2 h5
  field_simp [h10, h15, h25]
  ring

/-- The complete Euler and origin terms leave exactly the negative kernel-origin correction. -/
theorem metric_euler_origin_collector (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (m g : K[X]) (hm : m.natDegree ≤ p - 2)
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    -(4 / 9 : K) * originPole (T (-(p : ℤ)) * metricDuCleared p m g) -
      (25 / 18 : K) * originPole (metricDvCleared p m g) +
      (55 / 24 : K) * originPole (T (p : ℤ) * metricDvCleared p m g) +
      (11 / 6 : K) * m.coeff 0 =
        -m.coeff 0 / 4 + 4 * m.eval (1 / 4) / 75 + 27 * m.eval 4 / 100 := by
  rw [metric_du_high_origin p hp m g hm hg ha hb,
    metric_dv_origin p hp m g hg ha hb, metric_dv_frobenius_origin p hp m g hg ha hb]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num]; exact pow_ne_zero 2 h2
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]; exact mul_ne_zero h2 h3
  have h9 : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 ^ 2 by norm_num]; exact pow_ne_zero 2 h3
  have h18 : (18 : K) ≠ 0 := by
    rw [show (18 : K) = 2 * 3 ^ 2 by norm_num]; exact mul_ne_zero h2 (pow_ne_zero 2 h3)
  have h24 : (24 : K) ≠ 0 := by
    rw [show (24 : K) = 3 * 2 ^ 3 by norm_num]; exact mul_ne_zero h3 (pow_ne_zero 3 h2)
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by norm_num]; exact pow_ne_zero 2 h5
  have h50 : (50 : K) ≠ 0 := by
    rw [show (50 : K) = 2 * 5 ^ 2 by norm_num]; exact mul_ne_zero h2 (pow_ne_zero 2 h5)
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by norm_num]; exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have h100 : (100 : K) ≠ 0 := by
    rw [show (100 : K) = 2 ^ 2 * 5 ^ 2 by norm_num]
    exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h5)
  field_simp [h2, h4, h6, h9, h18, h24, h25, h50, h75, h100]
  ring

/-- The full Euler and literal origin sources are collected before canceling m(0). -/
theorem metric_complete_euler_origin_collector (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (m g : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2)
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    -originPole ((LaurentPolynomial.C (5 / 24 : ZMod p) * T (p : ℤ) *
        (4 * T (p : ℤ) - 11) + LaurentPolynomial.C (1 / 9 : ZMod p) *
          (4 * T (-(p : ℤ)) - 11)) * metricDuCleared p m g) -
      (25 / 18 : ZMod p) * originPole (metricDvCleared p m g) +
      (55 / 24 : ZMod p) * originPole (T (p : ℤ) * metricDvCleared p m g) +
      (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) *
        T (-1) * m.toLaurent).coeff (-1) =
      -m.coeff 0 / 4 + 4 * m.eval (1 / 4) / 75 + 27 * m.eval 4 / 100 := by
  rw [metric_du_positive_euler_origin, metric_logarithmic_origin p hp m hm]
  exact metric_euler_origin_collector p hp m g hm hg ha hb

end WPFieldAssembly.ActualBpairContraction
