import WPFieldAssembly.ActualBpairLowHBranchTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The literal cleared numerator from IR71j; its identification with the original
kernel derivative is a separate attachment to the root-owned source. -/
noncomputable def lowHKernelDerivativeBands (p : ℕ) : K[T;T⁻¹] :=
  (1 - T ((p - 1 : ℕ) : ℤ)) *
    (LaurentPolynomial.C (20 : K) * T 1 + LaurentPolynomial.C (15 / 2 : K) +
      (LaurentPolynomial.C (113 / 2 : K) * T 1 + LaurentPolynomial.C (4 : K)) * T (-(p : ℤ)) +
      (LaurentPolynomial.C (1953 / 8 : K) * T 1 - LaurentPolynomial.C (113 / 2 : K)) *
        T (-2 * (p : ℤ)))

/-- Every positive, negative and origin band is retained before coefficient selection. -/
theorem lowHKernelDerivativeBands_full (p : ℕ) (hp : 1 ≤ p) :
    lowHKernelDerivativeBands (K := K) p =
      LaurentPolynomial.C (20 : K) * T 1 + LaurentPolynomial.C (15 / 2 : K) * T 0 +
      LaurentPolynomial.C (113 / 2 : K) * T (1 - (p : ℤ)) +
      LaurentPolynomial.C (4 : K) * T (-(p : ℤ)) +
      LaurentPolynomial.C (1953 / 8 : K) * T (1 - 2 * (p : ℤ)) -
      LaurentPolynomial.C (113 / 2 : K) * T (-2 * (p : ℤ)) -
      LaurentPolynomial.C (20 : K) * T (p : ℤ) -
      LaurentPolynomial.C (15 / 2 : K) * T ((p : ℤ) - 1) -
      LaurentPolynomial.C (113 / 2 : K) * T 0 -
      LaurentPolynomial.C (4 : K) * T (-1) -
      LaurentPolynomial.C (1953 / 8 : K) * T (-(p : ℤ)) +
      LaurentPolynomial.C (113 / 2 : K) * T (-(p : ℤ) - 1) := by
  have hs : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
  have ha : (T ((p : ℤ) - 1) * T 1 : K[T;T⁻¹]) = T (p : ℤ) := by
    rw [← T_add]; congr 1; omega
  have hb : (T ((p : ℤ) - 1) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-1) := by
    rw [← T_add]; congr 1; omega
  have hc : (T ((p : ℤ) - 1) * T (-2 * (p : ℤ)) : K[T;T⁻¹]) = T (-(p : ℤ) - 1) := by
    rw [← T_add]; congr 1; omega
  have hd : (T 1 * T (-(p : ℤ)) : K[T;T⁻¹]) = T (1 - (p : ℤ)) := by
    rw [← T_add]; congr 1
  have he : (T 1 * T (-2 * (p : ℤ)) : K[T;T⁻¹]) = T (1 - 2 * (p : ℤ)) := by
    rw [← T_add]; congr 1
  have hf : (T ((p : ℤ) - 1) * T 1 * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, ← T_add, show (p : ℤ) - 1 + 1 + -p = 0 by omega, T_zero]
  have hg : (T ((p : ℤ) - 1) * T 1 * T (-2 * (p : ℤ)) : K[T;T⁻¹]) = T (-(p : ℤ)) := by
    rw [← T_add, ← T_add]; congr 1; omega
  simp only [lowHKernelDerivativeBands, hs, T_zero, mul_one]
  linear_combination LaurentPolynomial.C (113 / 2 : K) * hd +
    LaurentPolynomial.C (1953 / 8 : K) * he - LaurentPolynomial.C (20 : K) * ha -
    LaurentPolynomial.C (113 / 2 : K) * hf - LaurentPolynomial.C (4 : K) * hb -
    LaurentPolynomial.C (1953 / 8 : K) * hg + LaurentPolynomial.C (113 / 2 : K) * hc

private theorem lowH_origin_shift_band (p : ℕ) (hp : 3 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 2) (c : K) (s n : ℤ)
    (hn : 0 ≤ s + n ∨ s + n ≤ -((p : ℤ) - 1) ∨ s + n = -1) :
    (T s * (LaurentPolynomial.C c * T n) * R.toLaurent).coeff (-1) =
      if s + n = -1 then c * R.coeff 0 else 0 := by
  have he : T s * (LaurentPolynomial.C c * T n) * R.toLaurent =
      LaurentPolynomial.C c * T (s + n) * R.toLaurent := by rw [T_add]; ring
  rw [he]
  have hc := WPFiniteJCarrier.shifted_coeff c (s + n) (-1) R.toLaurent
  rw [hc]
  by_cases hz : s + n = -1
  · rw [if_pos hz, hz, show (-1 : ℤ) - -1 = 0 by omega]
    exact congrArg (c * ·) (WPFiniteJCarrier.toLaurent_coeff_nat R 0)
  · rw [if_neg hz]
    rcases hn with hpos | hneg | heq
    · rw [WPFiniteJCarrier.toLaurent_coeff_outside R _ (Or.inl (by omega)), mul_zero]
    · rw [WPFiniteJCarrier.toLaurent_coeff_outside R _ (Or.inr (by omega)), mul_zero]
    · exact (hz heq).elim

theorem lowH_kernel_origin_zero_phase (p : ℕ) (hp : 3 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 2) :
    (lowHKernelDerivativeBands (K := K) p * R.toLaurent).coeff (-1) =
      -4 * R.coeff 0 := by
  have he := lowHKernelDerivativeBands_full (K := K) p (by omega)
  have hm : lowHKernelDerivativeBands (K := K) p * R.toLaurent =
      T 0 * lowHKernelDerivativeBands p * R.toLaurent := by rw [T_zero, one_mul]
  rw [hm, he]
  simp only [mul_add, mul_sub, add_mul, sub_mul, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply]
  simp (disch := omega) only [lowH_origin_shift_band p hp R hR,
    if_pos (by omega : (0 : ℤ) + -1 = -1),
    if_neg (by omega : ¬(0 : ℤ) + 1 = -1),
    if_neg (by omega : ¬(0 : ℤ) + 0 = -1),
    if_neg (by omega : ¬(0 : ℤ) + (1 - (p : ℤ)) = -1),
    if_neg (by omega : ¬(0 : ℤ) + -(p : ℤ) = -1),
    if_neg (by omega : ¬(0 : ℤ) + (1 - 2 * (p : ℤ)) = -1),
    if_neg (by omega : ¬(0 : ℤ) + -2 * (p : ℤ) = -1),
    if_neg (by omega : ¬(0 : ℤ) + (p : ℤ) = -1),
    if_neg (by omega : ¬(0 : ℤ) + ((p : ℤ) - 1) = -1),
    if_neg (by omega : ¬(0 : ℤ) + (-(p : ℤ) - 1) = -1)]
  ring

theorem lowH_kernel_origin_negative_phase (p : ℕ) (hp : 3 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 2) :
    (T (-(p : ℤ)) * lowHKernelDerivativeBands (K := K) p * R.toLaurent).coeff (-1) =
      -(15 / 2 : K) * R.coeff 0 := by
  rw [lowHKernelDerivativeBands_full p (by omega)]
  simp only [mul_add, mul_sub, add_mul, sub_mul, AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_sub, Finsupp.add_apply, Finsupp.sub_apply]
  simp (disch := omega) only [lowH_origin_shift_band p hp R hR,
    if_pos (by omega : -(p : ℤ) + ((p : ℤ) - 1) = -1),
    if_neg (by omega : ¬-(p : ℤ) + 1 = -1),
    if_neg (by omega : ¬-(p : ℤ) + 0 = -1),
    if_neg (by omega : ¬-(p : ℤ) + (1 - (p : ℤ)) = -1),
    if_neg (by omega : ¬-(p : ℤ) + -(p : ℤ) = -1),
    if_neg (by omega : ¬-(p : ℤ) + (1 - 2 * (p : ℤ)) = -1),
    if_neg (by omega : ¬-(p : ℤ) + -2 * (p : ℤ) = -1),
    if_neg (by omega : ¬-(p : ℤ) + (p : ℤ) = -1),
    if_neg (by omega : ¬-(p : ℤ) + -1 = -1),
    if_neg (by omega : ¬-(p : ℤ) + (-(p : ℤ) - 1) = -1)]
  ring

/-- The two surviving diagonals are printed; no coefficient of R is discarded before its bound. -/
theorem lowH_kernel_origin_two_phases (p : ℕ) (hp : 3 ≤ p) (R : K[X])
    (hR : R.natDegree < p - 2) (α β : K) :
    ((LaurentPolynomial.C α * T (-(p : ℤ)) + LaurentPolynomial.C β) *
      lowHKernelDerivativeBands (K := K) p * R.toLaurent).coeff (-1) =
      (-(15 / 2 : K) * α - 4 * β) * R.coeff 0 := by
  rw [show (LaurentPolynomial.C α * T (-(p : ℤ)) + LaurentPolynomial.C β) *
      lowHKernelDerivativeBands (K := K) p * R.toLaurent =
      LaurentPolynomial.C α * (T (-(p : ℤ)) * lowHKernelDerivativeBands p * R.toLaurent) +
      LaurentPolynomial.C β * (lowHKernelDerivativeBands p * R.toLaurent) by ring]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, C_mul_coeff, C_mul_coeff,
    lowH_kernel_origin_negative_phase p hp R hR, lowH_kernel_origin_zero_phase p hp R hR]
  ring

theorem lowH_origin_quotient_Dstar_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHBranchYQuotient H * Dstar p).natDegree < p - 2 := by
  have hb := lowH_prime_six_band p hp
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have hQ := lowHBranchYQuotient_degree (p / 6) (by omega) H hH
  have hD := Dstar_degree (K := K) p hp
  have he := natDegree_mul_le (p := lowHBranchYQuotient H) (q := (Dstar p : K[X]))
  omega

theorem lowH_origin_quotient_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHBranchYQuotient H).coeff 0 = -(lowHCubicY H).coeff 0 / 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have he := congrArg (fun P : K[X] => P.eval 0) (lowHBranchYQuotient_source H h0)
  simp only [eval_mul, WPFiniteZSource.Abar, eval_sub, eval_X,
    eval_ofNat, eval_one, mul_zero, sub_zero] at he
  rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
  apply (eq_div_iff h4).mpr
  linear_combination he

/-- This is the original D-slot origin contribution, with y(0) and D(0) retained. -/
theorem lowH_original_D_kernel_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    ((LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K)) *
      lowHKernelDerivativeBands (K := K) p *
        (lowHBranchYQuotient H * Dstar p).toLaurent).coeff (-1) =
      (3 / 10 : K) * (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h10 : (10 : K) ≠ 0 := by convert mul_ne_zero h2 h5 using 1; norm_num
  rw [show LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (6 / 5 : K) =
      LaurentPolynomial.C (4 / 5 : K) * T (-(p : ℤ)) + LaurentPolynomial.C (-(6 / 5 : K)) by
    rw [map_neg, sub_eq_add_neg]]
  rw [lowH_kernel_origin_two_phases p (by omega) _
    (lowH_origin_quotient_Dstar_degree p hp H hH), mul_coeff_zero,
    lowH_origin_quotient_value p hp H h0]
  field_simp [h2, h4, h5, h10]
  ring

/-- The q2/kappa slot retains its own original origin term for later whole-source cancellation. -/
theorem lowH_original_constant_kernel_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0)
    (q2 κ : K) :
    ((LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3)) *
      lowHKernelDerivativeBands (K := K) p * (lowHBranchYQuotient H).toLaurent).coeff (-1) =
      (q2 / 2 - κ / 3) * (lowHCubicY H).coeff 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hd := lowHBranchYQuotient_degree (p / 6) (by omega) H hH
  have hs := lowH_prime_six_band p hp
  rw [show LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) - LaurentPolynomial.C (κ / 3) =
      LaurentPolynomial.C (4 * q2 / 15 : K) * T (-(p : ℤ)) + LaurentPolynomial.C (-(κ / 3)) by
    rw [map_neg, sub_eq_add_neg]]
  rw [lowH_kernel_origin_two_phases p (by omega) _ (by omega), lowH_origin_quotient_value p hp H h0]
  field_simp [h2, h3, h4, h15]
  ring

end WPFieldAssembly.ActualBpairContraction
