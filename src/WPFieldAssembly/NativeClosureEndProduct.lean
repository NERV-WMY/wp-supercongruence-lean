import WPFieldAssembly.ActualSimplePoleResidue
import WPFieldAssembly.ActualBpairMixedTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/-- The entire band at or above p, restored to its original polynomial phase. -/
noncomputable def endProductHigh (p : ℕ) (P : K[X]) : K[X] :=
  X ^ p * trunc (T (-(p : ℤ)) * P.toLaurent)

/-- Its complement retains exactly the indices strictly below p. -/
noncomputable def endProductLow (p : ℕ) (P : K[X]) : K[X] :=
  P - endProductHigh p P

noncomputable def endProductKernel (p : ℕ) (k0 k1 k2 : K[X]) : K[T;T⁻¹] :=
  k0.toLaurent + T (-(p : ℤ)) * k1.toLaurent +
    T (-2 * (p : ℤ)) * k2.toLaurent

noncomputable def endProductSource (p : ℕ) (w0 w1 : K[X]) : K[T;T⁻¹] :=
  w0.toLaurent + T (-(p : ℤ)) * w1.toLaurent

theorem endProductHigh_coeff (p : ℕ) (P : K[X]) (j : ℕ) :
    (endProductHigh p P).coeff j = if p ≤ j then P.coeff j else 0 := by
  rw [endProductHigh, coeff_X_pow_mul', WPFiniteJWeightedResidue.trunc_coeff]
  split_ifs with hj
  · have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ))
      ((j - p : ℕ) : ℤ) P.toLaurent
    simp only [map_one, one_mul] at hs
    rw [hs, show ((j - p : ℕ) : ℤ) - -(p : ℤ) = (j : ℤ) by omega,
      WPFiniteJCarrier.toLaurent_coeff_nat]
  · rfl

theorem endProductLow_coeff (p : ℕ) (P : K[X]) (j : ℕ) :
    (endProductLow p P).coeff j = if j < p then P.coeff j else 0 := by
  rw [endProductLow, coeff_sub, endProductHigh_coeff]
  by_cases hj : p ≤ j
  · rw [if_pos hj, if_neg (Nat.not_lt.mpr hj), sub_self]
  · rw [if_neg hj, if_pos (Nat.lt_of_not_ge hj), sub_zero]

theorem endProductHigh_add (p : ℕ) (P Q : K[X]) :
    endProductHigh p (P + Q) = endProductHigh p P + endProductHigh p Q := by
  simp only [endProductHigh, map_add, mul_add]

theorem endProductHigh_C_mul (p : ℕ) (c : K) (P : K[X]) :
    endProductHigh p (Polynomial.C c * P) = Polynomial.C c * endProductHigh p P := by
  ext j
  simp only [endProductHigh_coeff, coeff_C_mul]
  split_ifs <;> simp

theorem endProductHigh_small (p : ℕ) (P : K[X]) (hP : P.natDegree < p) :
    endProductHigh p P = 0 := by
  ext j
  rw [endProductHigh_coeff, coeff_zero]
  split_ifs with hj
  · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rfl

theorem endProduct_trunc_negative_phase (p m : ℕ) (P : K[X])
    (hP : P.natDegree < m * p) :
    trunc (T (-((m * p : ℕ) : ℤ)) * P.toLaurent) = 0 := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff, coeff_zero]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-((m * p : ℕ) : ℤ))
    (j : ℤ) P.toLaurent
  simp only [map_one, one_mul] at hs
  rw [hs, show (j : ℤ) - -((m * p : ℕ) : ℤ) = ((m * p + j : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Every negative phase is multiplied before any support is removed. -/
theorem endProduct_four_phases (p : ℕ) (k0 k1 k2 w0 w1 : K[X]) :
    endProductKernel p k0 k1 k2 * endProductSource p w0 w1 =
      (k0 * w0).toLaurent +
        T (-(p : ℤ)) * (k1 * w0 + k0 * w1).toLaurent +
        T (-2 * (p : ℤ)) * (k2 * w0 + k1 * w1).toLaurent +
        T (-3 * (p : ℤ)) * (k2 * w1).toLaurent := by
  have h2 : (T (-(p : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-2 * (p : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  have h3 : (T (-2 * (p : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) =
      T (-3 * (p : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  simp only [endProductKernel, endProductSource, map_add, map_mul]
  linear_combination k1.toLaurent * w1.toLaurent * h2 +
    k2.toLaurent * w1.toLaurent * h3

theorem endProduct_kernel_regular (p : ℕ) (k0 k1 k2 : K[X])
    (hk1 : k1.natDegree < p) (hk2 : k2.natDegree < 2 * p) :
    trunc (endProductKernel p k0 k1 k2) = k0 := by
  rw [endProductKernel, map_add, map_add, trunc_toLaurent]
  have h1 := endProduct_trunc_negative_phase p 1 k1 (by simpa using hk1)
  have h2 := endProduct_trunc_negative_phase p 2 k2 hk2
  simp only [one_mul, Nat.cast_mul, Nat.cast_ofNat, ← neg_mul] at h1 h2
  rw [h1, h2, add_zero, add_zero]

/-- The first p slot is retained; the second and third bands disappear by their degrees. -/
theorem endProduct_regular (p : ℕ) (k0 k1 k2 w0 w1 : K[X])
    (h2 : (k2 * w0 + k1 * w1).natDegree < 2 * p)
    (h3 : (k2 * w1).natDegree < 3 * p) :
    trunc (endProductKernel p k0 k1 k2 * endProductSource p w0 w1) =
      k0 * w0 + trunc (T (-(p : ℤ)) * (k1 * w0 + k0 * w1).toLaurent) := by
  rw [endProduct_four_phases, map_add, map_add, map_add, trunc_toLaurent]
  have hz2 := endProduct_trunc_negative_phase p 2 (k2 * w0 + k1 * w1) h2
  have hz3 := endProduct_trunc_negative_phase p 3 (k2 * w1) h3
  simp only [Nat.cast_mul, Nat.cast_ofNat, ← neg_mul] at hz2 hz3
  rw [hz2, hz3, add_zero, add_zero]

private theorem endProduct_DD_origin_single (a ai c : K) (n : ℤ) :
    (DD a ai (LaurentPolynomial.C c * T n)).coeff (-1) =
      if n < 0 then -c * ai ^ (-n).toNat else 0 := by
  rw [DD_monomial, C_mul_coeff]
  cases n with
  | ofNat n =>
    rw [monQ, forward_coeff]
    change c * (if 0 ≤ (-1 : ℤ) ∧ -1 < (n : ℤ) then
      a ^ ((n : ℤ) - 1 - (-1)).toNat else 0) =
        if (n : ℤ) < 0 then -c * ai ^ (-(n : ℤ)).toNat else 0
    simp only [show ¬(0 ≤ (-1 : ℤ) ∧ -1 < (n : ℤ)) by omega,
      if_false, mul_zero, show ¬((n : ℤ) < 0) by omega]
  | negSucc n =>
    rw [monQ, ← map_neg (LaurentPolynomial.C : K →+* K[T;T⁻¹]),
      shift_coeff, forward_coeff]
    rw [show (-1 : ℤ) - (-(n + 1 : ℤ)) = (n : ℤ) by omega,
      if_pos (by omega : 0 ≤ (n : ℤ) ∧ (n : ℤ) < ((n + 1 : ℕ) : ℤ))]
    simp only [show (((n + 1 : ℕ) : ℤ) - 1 - (n : ℤ)).toNat = 0 by omega,
      pow_zero, mul_one, show Int.negSucc n < 0 by omega, if_true]
    rw [show (-(Int.negSucc n)).toNat = n + 1 by omega]
    ring

theorem endProduct_pole_origin (a ai : K) (F : K[T;T⁻¹]) :
    (DD a ai F).coeff (-1) = -(trunc (invert F)).eval ai + F.coeff 0 := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, eval_add]
    rw [hF, hG]
    ring
  | C_mul_T n c =>
    rw [endProduct_DD_origin_single]
    simp only [map_mul, invert_C, invert_T, trunc_C_mul_T,
      C_mul_coeff, T_apply]
    by_cases hn : n < 0
    · rw [if_pos hn, if_pos (by omega : 0 ≤ -n), if_neg (by omega : n ≠ (0 : ℤ)),
        eval_monomial]
      ring
    · rw [if_neg hn]
      by_cases hz : n = 0
      · subst n
        simp
      · rw [if_neg (by omega : ¬0 ≤ -n), if_neg hz]
        simp

/-- Full Laurent evaluation splits into its regular and negative parts, retaining origin once. -/
theorem endProduct_evaluation_split (F : K[T;T⁻¹]) (a : K) (ha : a ≠ 0) :
    (trunc (invert F)).eval a⁻¹ - F.coeff 0 =
      ev a ha F - (trunc F).eval a := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG =>
    simp only [map_add, eval_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [show (trunc (invert F)).eval a⁻¹ + (trunc (invert G)).eval a⁻¹ -
        (F.coeff 0 + G.coeff 0) =
      ((trunc (invert F)).eval a⁻¹ - F.coeff 0) +
        ((trunc (invert G)).eval a⁻¹ - G.coeff 0) by ring, hF, hG]
    ring
  | C_mul_T n c =>
    have hev : ev a ha (LaurentPolynomial.C c * T n) = c * a ^ n := by
      simp [ev]
    rw [hev]
    simp only [map_mul, invert_C, invert_T, trunc_C_mul_T, C_mul_coeff, T_apply]
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast]
      by_cases hn : n = 0
      · subst n
        simp
      · rw [if_pos (by omega : 0 ≤ (n : ℤ)),
          if_neg (by omega : ¬0 ≤ -(n : ℤ)),
          if_neg (by omega : (n : ℤ) ≠ (0 : ℤ))]
        simp
    | negSucc n =>
      rw [if_pos (by omega : 0 ≤ -(Int.negSucc n)),
        if_neg (by omega : ¬0 ≤ Int.negSucc n),
        if_neg (by omega : Int.negSucc n ≠ (0 : ℤ))]
      simp [zpow_negSucc]

theorem endProduct_pole_evaluation (F : K[T;T⁻¹]) (a : K) (ha : a ≠ 0) :
    (DD a a⁻¹ F).coeff (-1) = (trunc F).eval a - ev a ha F := by
  rw [endProduct_pole_origin]
  have he := endProduct_evaluation_split F a ha
  linear_combination -he

theorem endProduct_shifted_evaluation (P : K[X]) (s : ℤ) (a : K) (ha : a ≠ 0) :
    ev a ha (T s * P.toLaurent) = a ^ s * P.eval a := by
  rw [map_mul]
  have ht : ev a ha (T s : K[T;T⁻¹]) = a ^ s := by
    simp [ev]
  rw [ht]
  simp [ev, LaurentPolynomial.eval₂_toLaurent]

theorem endProduct_source_evaluation (p : ℕ) (w0 w1 : K[X]) (a : K) (ha : a ≠ 0) :
    ev a ha (endProductSource p w0 w1) =
      w0.eval a + a ^ (-(p : ℤ)) * w1.eval a := by
  rw [endProductSource, map_add, endProduct_shifted_evaluation]
  simp [ev, LaurentPolynomial.eval₂_toLaurent]

theorem endProduct_high_phase_evaluation (p : ℕ) (P : K[X]) (a : K) (ha : a ≠ 0) :
    a ^ (-(p : ℤ)) * (endProductHigh p P).eval a =
      (trunc (T (-(p : ℤ)) * P.toLaurent)).eval a := by
  rw [endProductHigh, eval_mul, eval_pow, eval_X, zpow_neg, zpow_natCast,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero p ha), one_mul]

theorem endProduct_low_sub_high_evaluation (p : ℕ) (P Q : K[X])
    (a : K) (ha : a ≠ 0) :
    a ^ (-(p : ℤ)) * (endProductLow p P - endProductHigh p Q).eval a =
      a ^ (-(p : ℤ)) * P.eval a -
        (trunc (T (-(p : ℤ)) * (Q + P).toLaurent)).eval a := by
  have hp := endProduct_high_phase_evaluation p P a ha
  have hq := endProduct_high_phase_evaluation p Q a ha
  simp only [endProductLow, eval_sub] at *
  simp only [map_add, mul_add, eval_add]
  linear_combination -hp - hq

/-- SB107e: the whole three-band kernel and two-band source cancel with both
original endpoint poles before the inclusive first tail is collected. -/
theorem endProduct_whole_cancellation (p : ℕ) (k0 k1 k2 w0 w1 : K[X]) (q : K)
    (h4 : (4 : K) ≠ 0) (hk1 : k1.natDegree < p) (hk2 : k2.natDegree < 2 * p)
    (h2 : (k2 * w0 + k1 * w1).natDegree < 2 * p)
    (h3 : (k2 * w1).natDegree < 3 * p)
    (ha : w0.eval (1 / 4) + (1 / 4 : K) ^ (-(p : ℤ)) * w1.eval (1 / 4) = q)
    (hb : w0.eval 4 + (4 : K) ^ (-(p : ℤ)) * w1.eval 4 = -q) :
    -2 * (DD (1 / 4 : K) 4
      (endProductKernel p k0 k1 k2 * endProductSource p w0 w1)).coeff (-1) -
      (DD (4 : K) (1 / 4)
        (endProductKernel p k0 k1 k2 * endProductSource p w0 w1)).coeff (-1) +
      2 * q * (DD (1 / 4 : K) 4 (endProductKernel p k0 k1 k2)).coeff (-1) -
      q * (DD (4 : K) (1 / 4) (endProductKernel p k0 k1 k2)).coeff (-1) =
      2 * (1 / 4 : K) ^ (-(p : ℤ)) *
        (endProductLow p (k0 * w1) - endProductHigh p (k1 * w0)).eval (1 / 4) +
      (4 : K) ^ (-(p : ℤ)) *
        (endProductLow p (k0 * w1) - endProductHigh p (k1 * w0)).eval 4 := by
  have ha0 : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  let A := endProductKernel p k0 k1 k2
  let B := endProductSource p w0 w1
  have hpa (F : K[T;T⁻¹]) : (DD (1 / 4 : K) 4 F).coeff (-1) =
      (trunc F).eval (1 / 4) - ev (1 / 4) ha0 F := by
    simpa only [one_div, inv_inv] using endProduct_pole_evaluation F (1 / 4) ha0
  have hpb (F : K[T;T⁻¹]) : (DD (4 : K) (1 / 4) F).coeff (-1) =
      (trunc F).eval 4 - ev 4 h4 F := by
    simpa only [one_div] using endProduct_pole_evaluation F 4 h4
  have hBa : ev (1 / 4) ha0 B = q := by
    exact (endProduct_source_evaluation p w0 w1 (1 / 4) ha0).trans ha
  have hBb : ev 4 h4 B = -q := by
    exact (endProduct_source_evaluation p w0 w1 4 h4).trans hb
  have hA := endProduct_kernel_regular p k0 k1 k2 hk1 hk2
  have hAB := endProduct_regular p k0 k1 k2 w0 w1 h2 h3
  have hla := endProduct_low_sub_high_evaluation p (k0 * w1) (k1 * w0) (1 / 4) ha0
  have hlb := endProduct_low_sub_high_evaluation p (k0 * w1) (k1 * w0) 4 h4
  simp only [eval_mul] at hla hlb
  change -2 * (DD (1 / 4 : K) 4 (A * B)).coeff (-1) -
      (DD (4 : K) (1 / 4) (A * B)).coeff (-1) +
      2 * q * (DD (1 / 4 : K) 4 A).coeff (-1) -
      q * (DD (4 : K) (1 / 4) A).coeff (-1) = _
  have hea : ev (1 / 4) ha0 (A * B) = ev (1 / 4) ha0 A * q := by
    rw [(ev (1 / 4) ha0).map_mul, hBa]
  have heb : ev 4 h4 (A * B) = ev 4 h4 A * -q := by
    rw [(ev 4 h4).map_mul, hBb]
  rw [hpa, hpb, hpa, hpb, hea, heb]
  change -2 * ((trunc (A * B)).eval (1 / 4) - ev (1 / 4) ha0 A * q) -
      ((trunc (A * B)).eval 4 - ev 4 h4 A * -q) +
      2 * q * ((trunc A).eval (1 / 4) - ev (1 / 4) ha0 A) -
      q * ((trunc A).eval 4 - ev 4 h4 A) = _
  change trunc A = k0 at hA
  change trunc (A * B) = _ at hAB
  rw [hA, hAB]
  simp only [eval_add, eval_mul]
  linear_combination -2 * k0.eval (1 / 4) * ha - k0.eval 4 * hb - 2 * hla - hlb

end WPFieldAssembly.ActualBpairContraction
