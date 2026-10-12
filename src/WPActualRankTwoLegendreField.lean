import WPActualRankTwoGaussODE
import WPActualCMGauss

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter WPActualNativeSecondTaylor
  WPActualRankTwoParameter WPActualRankTwoGaussODE WPActualCMGauss

namespace WPActualRankTwoLegendreField

noncomputable def rankCoefficientPolynomial {K : Type*} [CommRing K]
    (e : ℕ) (a : ℕ → K) : K[X] :=
  ∑ n ∈ Finset.range (e + 1), Polynomial.monomial n (a n)

theorem rankCoefficientPolynomial_coeff {K : Type*} [CommRing K]
    (e n : ℕ) (a : ℕ → K) :
    (rankCoefficientPolynomial e a).coeff n = if n < e + 1 then a n else 0 := by
  classical
  simp only [rankCoefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < e + 1
  · rw [if_pos hn, Finset.sum_eq_single n]
    · simp
    · intro m _ hmn; simp [hmn]
    · simp [Finset.mem_range, hn]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m hm
    have hmn : m ≠ n := by have := Finset.mem_range.mp hm; omega
    simp [hmn]

theorem rankCoefficientPolynomial_degree {K : Type*} [CommRing K]
    (e : ℕ) (a : ℕ → K) : (rankCoefficientPolynomial e a).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [rankCoefficientPolynomial_coeff, if_neg (by omega)]

theorem rankCoefficientPolynomial_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (e : ℕ) (a : ℕ → K) :
    (rankCoefficientPolynomial e a).map f = rankCoefficientPolynomial e (fun n => f (a n)) := by
  simp [rankCoefficientPolynomial, Polynomial.map_sum, Polynomial.map_monomial]

/-- The common reduction of the two actual nodes, retaining the full original cutoff. -/
noncomputable def rankFieldPolynomial (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  rankCoefficientPolynomial (p - 1 - p / 6) (fun n => rankFieldCoefficient p n)

noncomputable def actualLegendreGauss (p : ℕ) : (ZMod p)[X] :=
  (shiftedLegendre (p / 6)).map (Int.castRingHom (ZMod p))

theorem rankFieldCoefficient_recurrence (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n + 1 < p) :
    36 * ((n : ZMod p) + 1) ^ 2 * rankFieldCoefficient p (n + 1) =
      (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5) * rankFieldCoefficient p n := by
  have hD := rankDenominator_origin_residue_ne_zero p n hp (by omega)
  have hDnext := rankDenominator_origin_residue_ne_zero p (n + 1) hp hn
  rw [rankDenominator_eval_succ] at hDnext
  have hB := (mul_ne_zero_iff.mp hDnext).2
  have hf (a u d b : ZMod p) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by
    field_simp [hd, hb]
  unfold rankFieldCoefficient
  rw [rankNumerator_eval_succ, rankDenominator_eval_succ]
  convert hf ((rankNumerator (ZMod p) n).eval 0)
    ((6 * (n : ZMod p) + 1 + 6 * 0) * (6 * (n : ZMod p) + 5 + 6 * 0))
    ((rankDenominator (ZMod p) n).eval 0)
    (36 * ((n : ZMod p) + 1) * ((n : ZMod p) + 1 + 0)) hD hB using 1 <;> ring

theorem rankField_eigenvalue (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * ((p / 6 : ℕ) : ZMod p) * (((p / 6 : ℕ) : ZMod p) + 1) = -5 := by
  have hprod : (6 * ((p / 6 : ℕ) : ZMod p) + 1) *
      (6 * ((p / 6 : ℕ) : ZMod p) + 5) = 0 := by
    rcases prime_six_classes p hp with h1 | h5
    · have h : 6 * ((p / 6 : ℕ) : ZMod p) + 1 = 0 := by
        have hc := congrArg (fun n : ℕ => (n : ZMod p)) h1
        simpa using hc.symm
      rw [h, zero_mul]
    · have h : 6 * ((p / 6 : ℕ) : ZMod p) + 5 = 0 := by
        have hc := congrArg (fun n : ℕ => (n : ZMod p)) h5
        simpa using hc.symm
      rw [h, mul_zero]
  linear_combination hprod

theorem rankField_legendre_factor (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (6 * (n : ZMod p) + 1) * (6 * (n : ZMod p) + 5) =
      36 * ((n : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
        ((n : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1) := by
  linear_combination rankField_eigenvalue p hp

theorem actualLegendreGauss_recurrence (p n : ℕ) :
    ((n : ZMod p) + 1) ^ 2 * (actualLegendreGauss p).coeff (n + 1) =
      ((n : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
        ((n : ZMod p) + ((p / 6 : ℕ) : ZMod p) + 1) *
          (actualLegendreGauss p).coeff n := by
  simp only [actualLegendreGauss, Polynomial.coeff_map]
  have h := congrArg (Int.castRingHom (ZMod p))
    (shiftedLegendre_cleared_recurrence (p / 6) n)
  simpa only [map_mul, map_pow, map_add, map_sub, map_natCast, map_one] using h

theorem rankFieldCoefficient_eq_legendre (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    rankFieldCoefficient p n = (actualLegendreGauss p).coeff n := by
  induction n with
  | zero => simp [rankFieldCoefficient, rankNumerator, rankDenominator,
      actualLegendreGauss, Polynomial.coeff_map, coeff_shiftedLegendre]
  | succ n ih =>
    have hprev := ih (by omega)
    have hr := rankFieldCoefficient_recurrence p n hp hn
    rw [rankField_legendre_factor p n hp, hprev] at hr
    have hl := actualLegendreGauss_recurrence p n
    have h36 : (36 : ZMod p) ≠ 0 := by
      have hD := rankDenominator_origin_residue_ne_zero p 1 hp (by omega)
      simpa [rankDenominator_eval_zero] using hD
    have hnext : ((n : ZMod p) + 1) ≠ 0 := by
      have hc : ((n : ZMod p) + 1) = ((n + 1 : ℕ) : ZMod p) := by simp
      rw [hc]
      intro hz
      have := Nat.le_of_dvd (by omega : 0 < n + 1)
        ((ZMod.natCast_eq_zero_iff _ _).mp hz)
      omega
    apply mul_left_cancel₀ (mul_ne_zero h36 (pow_ne_zero 2 hnext))
    linear_combination hr - 36 * hl

/-- The whole original common polynomial is the actual normalized Legendre polynomial. -/
theorem actual_rankField_legendre (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankFieldPolynomial p = actualLegendreGauss p := by
  ext n
  rw [rankFieldPolynomial, rankCoefficientPolynomial_coeff]
  split_ifs with hn
  · exact rankFieldCoefficient_eq_legendre p n hp (by omega)
  · symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hd : (actualLegendreGauss p).natDegree ≤ p / 6 := by
      unfold actualLegendreGauss
      exact Polynomial.natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])
    omega

/-- The original full actual node with coefficients in its proved integral model. -/
noncomputable def rankIntegralPolynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℕ) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p - 1 - p / 6)
    (fun n => if hn : n < p then rankIntegralCoefficient p n hp hn k else 0)

theorem rankIntegralPolynomial_value (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankIntegralPolynomial p hp k).map (integralRationals p).subtype =
      rankNodePolynomial p k := by
  ext n
  rw [Polynomial.coeff_map, rankIntegralPolynomial, rankCoefficientPolynomial_coeff,
    rankNodePolynomial, coefficientPolynomial_coeff]
  by_cases hn : n < p - 1 - p / 6 + 1
  · rw [if_pos hn, if_pos hn, dif_pos (by omega)]
    exact rankIntegralCoefficient_value p n hp (by omega) k
  · simp [hn]

theorem rankIntegralPolynomial_field (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankIntegralPolynomial p hp k).map (residueHom p) = rankFieldPolynomial p := by
  ext n
  rw [Polynomial.coeff_map, rankIntegralPolynomial, rankCoefficientPolynomial_coeff,
    rankFieldPolynomial, rankCoefficientPolynomial_coeff]
  by_cases hn : n < p - 1 - p / 6 + 1
  · rw [if_pos hn, if_pos hn, dif_pos (by omega)]
    exact rankIntegralCoefficient_residue p n hp (by omega) k
  · simp [hn]

noncomputable def integralHalf (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : integralRationals p :=
  ⟨1 / 2, WPFiniteConductorPolynomial.small_inverse_integral p 2 (by norm_num) (by omega)⟩

theorem integralHalf_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p (integralHalf p hp) = (1 / 2 : ZMod p) := by
  change ((1 / 2 : ℚ) : ZMod p) = (1 / 2 : ZMod p)
  norm_num [Rat.cast_def]

noncomputable def rankIntegralJacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (k : ℕ) :
    (integralRationals p)[X] :=
  (rankIntegralPolynomial p hp k).comp (C (integralHalf p hp) * (1 - X))

noncomputable def actualLegendreJacobi (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (actualLegendreGauss p).comp (C (1 / 2 : ZMod p) * (1 - X))

theorem rankIntegralJacobi_value (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankIntegralJacobi p hp k).map (integralRationals p).subtype = rankJacobiNode p k := by
  rw [rankIntegralJacobi, Polynomial.map_comp, rankIntegralPolynomial_value]
  simp [rankJacobiNode, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem rankIntegralJacobi_field (p k : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankIntegralJacobi p hp k).map (residueHom p) = actualLegendreJacobi p := by
  rw [rankIntegralJacobi, Polynomial.map_comp, rankIntegralPolynomial_field,
    actual_rankField_legendre p hp]
  simp [actualLegendreJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf_field]

theorem actual_rankJacobiCoefficient_integral (p k n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p ((rankJacobiNode p k).coeff n) := by
  rw [← rankIntegralJacobi_value p k hp, Polynomial.coeff_map]
  exact ((rankIntegralJacobi p hp k).coeff n).property

/-- Every coefficient of each original rational Jacobi node has the actual Legendre reduction. -/
theorem actual_rankJacobiCoefficient_legendre (p k n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((rankJacobiNode p k).coeff n : ZMod p) = (actualLegendreJacobi p).coeff n := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff n) (rankIntegralJacobi_value p k hp)
  have hr := congrArg (fun P : (ZMod p)[X] => P.coeff n) (rankIntegralJacobi_field p k hp)
  rw [Polynomial.coeff_map] at hv hr
  rw [← hv]
  exact hr

end WPActualRankTwoLegendreField
