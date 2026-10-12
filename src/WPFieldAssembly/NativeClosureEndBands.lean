import WPFieldAssembly.NativeClosureKernelValues
import WPFieldAssembly.ActualBpairLowHKernelAttachment

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteAffineLog

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: These are exactly the retained SB107 finite W0/W1
sources. Their whole Laurent support includes -p and the three canonical
0, -p and p coefficients before any endpoint specialization. The actual equality
to P-(actualAK+h)/3 remains in EndKernel, awaiting its Cubic prerequisite. -/

/-- The whole regular band of the original SB107 end source. -/
noncomputable def endKernelW0 (p : ℕ) : K[X] :=
  -Polynomial.C (6 / 5 : K) * Dstar p +
    Polynomial.C (11 * WPFiniteNC122.q p / 15 -
      (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2)

/-- The whole negative phase, including its genuine coefficient at -p. -/
noncomputable def endKernelW1 (p : ℕ) : K[X] :=
  Polynomial.C (4 / 5 : K) * Dstar p -
    Polynomial.C (2 / 15 : K) *
      ((LP p).comp (Polynomial.C (1 / 4 : K) * X) -
        (LP p).comp (Polynomial.C (4 : K) * X)) +
    Polynomial.C (4 * WPFiniteNC122.q p / 15)

/-- This finite source is defined before a fifth-root specialization. -/
noncomputable def endKernelChi0 (p : ℕ) : K[T;T⁻¹] :=
  (endKernelW0 p).toLaurent + T (-(p : ℤ)) * (endKernelW1 p).toLaurent

theorem endKernelW0_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (endKernelW0 p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  unfold endKernelW0
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [← Polynomial.C_neg]
    exact (natDegree_C_mul_le _ _).trans (Dstar_degree p hp)
  · simp

theorem endKernelW1_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (endKernelW1 p : K[X]).natDegree ≤ p - 1 := by
  have hd : (Dstar p : K[X]).natDegree ≤ p - 1 := (Dstar_degree p hp).trans (by omega)
  have hl (c : K) : ((LP p : K[X]).comp (Polynomial.C c * X)).natDegree ≤ p - 1 := by
    have hc : (Polynomial.C c * X : K[X]).natDegree ≤ 1 :=
      (natDegree_C_mul_le _ _).trans (by simp)
    exact natDegree_comp_le.trans
      ((Nat.mul_le_mul (LP_natDegree_le p) hc).trans (by simp))
  unfold endKernelW1
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans hd
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_sub_le _ _).trans (max_le (hl _) (hl _)))
  · simp

private theorem endKernelChi0_coeff (p : ℕ) (j : ℤ) :
    (endKernelChi0 p : K[T;T⁻¹]).coeff j =
      (endKernelW0 p : K[X]).toLaurent.coeff j +
        (endKernelW1 p : K[X]).toLaurent.coeff (j + p) := by
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) j
    (endKernelW1 p : K[X]).toLaurent
  simp only [map_one, one_mul] at hs
  rw [endKernelChi0, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hs]
  congr 1
  congr 1
  omega

/-- The entire source has the original -p through N-1 support; its -p slot remains. -/
theorem endKernelChi0_support (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (j : ℤ) (hj : j ∈ (endKernelChi0 p : K[T;T⁻¹]).coeff.support) :
    -(p : ℤ) ≤ j ∧ j ≤ (((p - 1) / 2 - 1 : ℕ) : ℤ) := by
  have hne := Finsupp.mem_support_iff.mp hj
  have h0 := endKernelW0_degree (K := K) p hp
  have h1 := endKernelW1_degree (K := K) p hp
  constructor
  · by_contra hn
    have hz0 := WPFiniteJCarrier.toLaurent_coeff_outside (endKernelW0 p : K[X]) j
      (Or.inl (by omega))
    have hz1 := WPFiniteJCarrier.toLaurent_coeff_outside (endKernelW1 p : K[X]) (j + p)
      (Or.inl (by omega))
    rw [endKernelChi0_coeff, hz0, hz1, zero_add] at hne
    exact hne rfl
  · by_contra hn
    have hz0 := WPFiniteJCarrier.toLaurent_coeff_outside (endKernelW0 p : K[X]) j
      (Or.inr (by omega))
    have hz1 := WPFiniteJCarrier.toLaurent_coeff_outside (endKernelW1 p : K[X]) (j + p)
      (Or.inr (by omega))
    rw [endKernelChi0_coeff, hz0, hz1, zero_add] at hne
    exact hne rfl

/-- All three canonical coefficients follow from the full source, before endpoint evaluation. -/
theorem endKernelChi0_invisible_coefficients (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endKernelChi0 p : K[T;T⁻¹]).coeff 0 =
      -(6 / 5 : K) * (Dstar p : K[X]).coeff 0 +
        11 * WPFiniteNC122.q p / 15 -
          (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 ∧
    (endKernelChi0 p : K[T;T⁻¹]).coeff (-(p : ℤ)) =
      (4 / 5 : K) * (Dstar p : K[X]).coeff 0 + 4 * WPFiniteNC122.q p / 15 ∧
    (endKernelChi0 p : K[T;T⁻¹]).coeff (p : ℤ) = 0 := by
  have h0 := endKernelW0_degree (K := K) p hp
  have h1 := endKernelW1_degree (K := K) p hp
  have hp0 : (endKernelW1 p : K[X]).toLaurent.coeff (p : ℤ) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hm0 : (endKernelW0 p : K[X]).toLaurent.coeff (-(p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))
  have hp1 : (endKernelW0 p : K[X]).toLaurent.coeff (p : ℤ) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hp2 : (endKernelW1 p : K[X]).toLaurent.coeff (2 * (p : ℤ)) = 0 :=
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hLP (c : K) : ((LP p : K[X]).comp (Polynomial.C c * X)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simp only [eval_mul, eval_C, eval_X, mul_zero]
    rw [LP, eval_finsetSum]
    apply Finset.sum_eq_zero
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Ico.mp hn).1; omega
    simp only [eval_mul, eval_C, eval_pow, eval_X, zero_pow hn0, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [endKernelChi0_coeff, zero_add, hp0, add_zero,
      ← show ((0 : ℕ) : ℤ) = 0 from rfl, WPFiniteJCarrier.toLaurent_coeff_nat]
    simp only [endKernelW0, neg_mul, coeff_add, coeff_neg, coeff_C_mul,
      coeff_C_zero]
    ring
  · rw [endKernelChi0_coeff, neg_add_cancel, hm0, zero_add,
      ← show ((0 : ℕ) : ℤ) = 0 from rfl, WPFiniteJCarrier.toLaurent_coeff_nat]
    simp only [endKernelW1, coeff_add, coeff_sub, coeff_C_mul, coeff_C_zero,
      hLP, sub_self, mul_zero, sub_zero]
  · rw [endKernelChi0_coeff, hp1, show (p : ℤ) + p = 2 * p by omega, hp2, zero_add]

end WPFieldAssembly.ActualBpairContraction
