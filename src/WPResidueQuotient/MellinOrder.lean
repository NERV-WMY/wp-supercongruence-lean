import WPResidueQuotient.MellinFactors
import Mathlib.RingTheory.LaurentSeries

/-!
# Actual rho orders of the Mellin coefficients

The valuation here is Mathlib's X-adic valuation of `RatFunc ℚ`, and the
order conclusion is about its actual embedding into `LaurentSeries ℚ`.
The lower-endpoint argument counts six inverse-H zeros and at most one
G pole. No regularity predicate or functional is assumed.
-/

noncomputable section

namespace WPResidueQuotient
namespace MellinFactors

open scoped BigOperators LaurentSeries WithZero RatFunc
open IsDedekindDomain.HeightOneSpectrum
open WithZero

/-- The existing X-adic valuation of the rational-function field. -/
abbrev rhoValuation : Valuation RF ℤᵐ⁰ := RatFunc.polynomialValuationX ℚ

theorem rhoValuation_polynomial_of_constant_ne_zero
    (p : Polynomial ℚ) (hp : p.coeff 0 ≠ 0) :
    rhoValuation (algebraMap (Polynomial ℚ) RF p) = 1 := by
  apply (valuation_eq_one_iff_notMem (v := Polynomial.idealX ℚ)).mpr
  intro hm
  have hd : Polynomial.X ∣ p := by
    exact Ideal.mem_span_singleton.mp hm
  exact hp (Polynomial.X_dvd_iff.mp hd)

theorem rhoValuation_constant (q : ℚ) (hq : q ≠ 0) :
    rhoValuation (q : RF) = 1 := by
  have hi : RatFunc.C q = (q : RF) := eq_ratCast RatFunc.C q
  rw [← hi, ← RatFunc.algebraMap_C]
  apply rhoValuation_polynomial_of_constant_ne_zero
  simpa only [Polynomial.coeff_C, if_true] using hq

/-- A linear factor with nonzero integer constant term has rho-order zero. -/
theorem rhoValuation_linearFactor_of_ne_zero
    (q : ℚ) (j : ℤ) (hj : j ≠ 0) :
    rhoValuation (linearFactor q j) = 1 := by
  rw [linearFactor_image]
  apply rhoValuation_polynomial_of_constant_ne_zero
  have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj
  simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, if_true, if_false, one_ne_zero, mul_zero, add_zero] using hjq

theorem rhoValuation_rho : rhoValuation rho = exp (-1 : ℤ) :=
  Polynomial.valuation_X_eq_neg_one ℚ

/-- The zero-index factor is exactly one simple rho-zero. -/
theorem rhoValuation_linearFactor_zero (q : ℚ) (hq : q ≠ 0) :
    rhoValuation (linearFactor q 0) = exp (-1 : ℤ) := by
  simp only [linearFactor, Int.cast_zero, zero_add, map_mul,
    rhoValuation_constant q hq, rhoValuation_rho, one_mul]

theorem rhoValuation_integerProduct_nat (q : ℚ) (n : ℕ) :
    rhoValuation (integerProduct q (n : ℤ)) = 1 := by
  rw [integerProduct_nat, map_prod]
  apply Finset.prod_eq_one
  intro j _
  apply rhoValuation_linearFactor_of_ne_zero
  omega

/-- Every negative centered product has exactly one simple rho-pole. -/
theorem rhoValuation_integerProduct_negSucc (q : ℚ) (hq : q ≠ 0) (n : ℕ) :
    rhoValuation (integerProduct q (Int.negSucc n)) = exp (1 : ℤ) := by
  rw [integerProduct_negSucc, map_inv₀, map_prod,
    Finset.prod_range_succ' (fun j => rhoValuation (linearFactor q (-(j : ℤ)))) n]
  have ht :
      (∏ j ∈ Finset.range n,
        rhoValuation (linearFactor q (-((j + 1 : ℕ) : ℤ)))) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    apply rhoValuation_linearFactor_of_ne_zero
    omega
  rw [ht]
  simp only [Nat.cast_zero, neg_zero,
    rhoValuation_linearFactor_zero q hq, one_mul, ← exp_neg]
  norm_num

/-- At every integer index there is at most one G pole. -/
theorem rhoValuation_G_le (k : ℤ) : rhoValuation (G k) ≤ exp (1 : ℤ) := by
  unfold G
  generalize hi : k - 1 = l
  cases l with
  | ofNat n =>
      change rhoValuation (integerProduct 6 (n : ℤ)) ≤ exp (1 : ℤ)
      rw [rhoValuation_integerProduct_nat]
      exact (show exp (0 : ℤ) ≤ exp (1 : ℤ) by
        rw [exp_le_exp]
        norm_num)
  | negSucc n =>
      rw [rhoValuation_integerProduct_negSucc 6 (by norm_num)]

/-- A negative H-index supplies exactly one inverse-H rho-zero. -/
theorem rhoValuation_inverseH_of_neg (l : ℤ) (hl : l < 0) :
    rhoValuation (inverseH l) = exp (-1 : ℤ) := by
  unfold inverseH H
  cases l with
  | ofNat n =>
      change (n : ℤ) < 0 at hl
      omega
  | negSucc n =>
      rw [map_inv₀, rhoValuation_integerProduct_negSucc 1 (by norm_num)]
      simp only [← exp_neg]

theorem rhoValuation_inverseH_le_one (l : ℤ) :
    rhoValuation (inverseH l) ≤ 1 := by
  unfold inverseH H
  cases l with
  | ofNat n =>
      change rhoValuation ((integerProduct 1 (n : ℤ))⁻¹) ≤ 1
      rw [map_inv₀, rhoValuation_integerProduct_nat]
      simp
  | negSucc n =>
      rw [map_inv₀, rhoValuation_integerProduct_negSucc 1 (by norm_num), ← exp_neg]
      exact (show exp (-1 : ℤ) ≤ exp (0 : ℤ) by
        rw [exp_le_exp]
        norm_num)

theorem rhoValuation_G_of_pos (k : ℤ) (hk : 0 < k) : rhoValuation (G k) = 1 := by
  unfold G
  generalize hi : k - 1 = l
  cases l with
  | ofNat n => exact rhoValuation_integerProduct_nat 6 n
  | negSucc n => omega

theorem rhoValuation_G_zero : rhoValuation (G 0) = exp (1 : ℤ) := by
  have hv6 : rhoValuation (6 : RF) = 1 := by
    simpa using rhoValuation_constant 6 (by norm_num)
  rw [G_zero, map_inv₀, map_mul, hv6,
    rhoValuation_rho, one_mul, ← exp_neg]
  norm_num

theorem coefficient_regular_of_pos (k : ℤ) (l : SixIndices) (hk : 0 < k) :
    rhoValuation (coefficient k l) ≤ 1 := by
  rw [coefficient, map_mul, rhoValuation_G_of_pos k hk, one_mul, map_prod]
  exact Finset.prod_le_one' (fun i _ => rhoValuation_inverseH_le_one (l i))

/-- At G-index zero, one negative H-index cancels its simple pole. -/
theorem coefficient_regular_at_zero (l : SixIndices) (i : Fin 6) (hi : l i < 0) :
    rhoValuation (coefficient 0 l) ≤ 1 := by
  rw [coefficient, map_mul, rhoValuation_G_zero, map_prod,
    Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)
      (fun j => rhoValuation (inverseH (l j))), rhoValuation_inverseH_of_neg (l i) hi]
  calc
    exp (1 : ℤ) * (exp (-1 : ℤ) *
        ∏ j ∈ Finset.univ \ {i}, rhoValuation (inverseH (l j))) =
        ∏ j ∈ Finset.univ \ {i}, rhoValuation (inverseH (l j)) := by
      rw [← mul_assoc, ← exp_add]
      norm_num
    _ ≤ 1 := Finset.prod_le_one' (fun j _ => rhoValuation_inverseH_le_one (l j))

theorem coefficient_regular (k : ℤ) (l : SixIndices) (hk : 0 ≤ k)
    (hz : k = 0 → ∃ i, l i < 0) : rhoValuation (coefficient k l) ≤ 1 := by
  by_cases hk0 : k = 0
  · obtain ⟨i, hi⟩ := hz hk0
    rw [hk0]
    exact coefficient_regular_at_zero l i hi
  · exact coefficient_regular_of_pos k l (by omega)

/-- Every allowed closed-pole coefficient is actually regular in rho. -/
theorem mellinTerm_regular_valuation
    (m n : ℤ) (a : ExponentVector) (hm : 1 ≤ m) (hn : 0 ≤ n)
    (ha : (∑ i, a i) ≤ m) : rhoValuation (mellinTerm m n a) ≤ 1 := by
  apply coefficient_regular
  · unfold poleIndex
    omega
  · intro hk0
    have hn0 : n = 0 := by unfold poleIndex at hk0; omega
    have hsum : 0 < ∑ i, a i := by unfold poleIndex at hk0; omega
    have hex : ∃ i, 0 < a i := by
      by_contra h
      push Not at h
      have hs : (∑ i, a i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
      omega
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    unfold denominatorIndices
    omega

/-- The regularity conclusion produces an actual formal power series,
rather than an assumed regularity hypothesis. -/
theorem mellinTerm_eq_powerSeries
    (m n : ℤ) (a : ExponentVector) (hm : 1 ≤ m) (hn : 0 ≤ n)
    (ha : (∑ i, a i) ≤ m) :
    ∃ P : PowerSeries ℚ, (P : LaurentSeries ℚ) = mellinTerm m n a := by
  apply (LaurentSeries.val_le_one_iff_eq_coe ℚ _).mp
  rw [LaurentSeries.valuation_coe_ratFunc, RatFunc.v_def]
  exact mellinTerm_regular_valuation m n a hm hn ha

theorem rhoValuation_six_inverseH (l : SixIndices) (hl : ∀ i, l i < 0) :
    rhoValuation (∏ i, inverseH (l i)) = exp (-6 : ℤ) := by
  rw [map_prod]
  have he : ∀ i, rhoValuation (inverseH (l i)) = exp (-1 : ℤ) :=
    fun i => rhoValuation_inverseH_of_neg (l i) (hl i)
  simp_rw [he]
  norm_num [← exp_nsmul]

/-- The actual rational-function valuation of each discarded lower term. -/
theorem coefficient_lowerEndpoint_valuation
    (k : ℤ) (l : SixIndices) (hl : ∀ i, l i < 0) :
    rhoValuation (coefficient k l) ≤ exp (-5 : ℤ) := by
  calc
    rhoValuation (coefficient k l) =
        rhoValuation (G k) * rhoValuation (∏ i, inverseH (l i)) := by
      rw [coefficient, map_mul]
    _ = rhoValuation (G k) * exp (-6 : ℤ) := by
      rw [rhoValuation_six_inverseH l hl]
    _ ≤ exp (1 : ℤ) * exp (-6 : ℤ) :=
      mul_le_mul_of_nonneg_right (rhoValuation_G_le k) zero_le
    _ = exp (-5 : ℤ) := by rw [← exp_add]; norm_num

/-- Every Laurent coefficient below rho-degree five is actually zero. -/
theorem coefficient_lowerEndpoint_coeff_zero
    (k : ℤ) (l : SixIndices) (hl : ∀ i, l i < 0) (d : ℤ) (hd : d < 5) :
    (coefficient k l : LaurentSeries ℚ).coeff d = 0 := by
  apply LaurentSeries.coeff_zero_of_lt_valuation ℚ _ hd
  rw [LaurentSeries.valuation_coe_ratFunc, RatFunc.v_def]
  exact coefficient_lowerEndpoint_valuation k l hl

/-- The lower endpoint has actual Laurent order at least five. -/
theorem coefficient_lowerEndpoint_order
    (k : ℤ) (l : SixIndices) (hl : ∀ i, l i < 0) :
    5 ≤ (coefficient k l : LaurentSeries ℚ).order := by
  apply le_of_not_gt
  intro hlt
  have hc := coefficient_lowerEndpoint_coeff_zero k l hl
    (coefficient k l : LaurentSeries ℚ).order hlt
  have hz : (coefficient k l : LaurentSeries ℚ) = 0 :=
    HahnSeries.coeff_order_eq_zero.mp hc
  have hmap :
      algebraMap RF (LaurentSeries ℚ) (coefficient k l) =
        algebraMap RF (LaurentSeries ℚ) 0 := by simpa using hz
  exact coefficient_ne_zero k l ((algebraMap RF (LaurentSeries ℚ)).injective hmap)

/-- For `n < min_i a_i`, all six denominator indices are negative. This
is the omitted lower endpoint of noncanonical exponent reindexing. -/
theorem mellinTerm_lowerEndpoint_order
    (m n : ℤ) (a : ExponentVector) (hn : ∀ i, n < a i) :
    5 ≤ (mellinTerm m n a : LaurentSeries ℚ).order := by
  apply coefficient_lowerEndpoint_order
  intro i
  unfold denominatorIndices
  exact sub_neg.mpr (hn i)

theorem mellinTerm_lowerEndpoint_coeff_zero
    (m n : ℤ) (a : ExponentVector) (hn : ∀ i, n < a i)
    (d : ℤ) (hd : d < 5) :
    (mellinTerm m n a : LaurentSeries ℚ).coeff d = 0 := by
  apply coefficient_lowerEndpoint_coeff_zero _ _ _ d hd
  intro i
  unfold denominatorIndices
  exact sub_neg.mpr (hn i)

end MellinFactors
end WPResidueQuotient
