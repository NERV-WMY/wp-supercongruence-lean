import WPActualRankTwoLegendreField

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter WPActualRankTwoParameter
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualCMGauss

namespace WPActualRankTwoFirstLift

theorem map_integer_polynomial {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (P : ℤ[X]) :
    (P.map (Int.castRingHom K)).map f = P.map (Int.castRingHom L) := by
  rw [Polynomial.map_map]
  congr 1
  ext z
  simp

/-- The normalized characteristic-zero Legendre polynomial in the printed T variable. -/
noncomputable def rationalLegendre (d : ℕ) : ℚ[X] :=
  ((shiftedLegendre d).map (Int.castRingHom ℚ)).comp (C (1 / 2) * (1 - X))

/-- The same polynomial in the actual integral coefficient model. -/
noncomputable def integralLegendre (p d : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  ((shiftedLegendre d).map (Int.castRingHom (integralRationals p))).comp
    (C (integralHalf p hp) * (1 - X))

theorem integralLegendre_value (p d : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralLegendre p d hp).map (integralRationals p).subtype = rationalLegendre d := by
  rw [integralLegendre, Polynomial.map_comp, map_integer_polynomial]
  simp [rationalLegendre, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem integralLegendre_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralLegendre p (p / 6) hp).map (residueHom p) = actualLegendreJacobi p := by
  rw [integralLegendre, Polynomial.map_comp, map_integer_polynomial]
  simp [actualLegendreJacobi, actualLegendreGauss, Polynomial.map_mul,
    Polynomial.map_sub, integralHalf_field]

theorem rationalLegendre_coefficient_integral (p d n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p ((rationalLegendre d).coeff n) := by
  rw [← integralLegendre_value p d hp, Polynomial.coeff_map]
  exact ((integralLegendre p d hp).coeff n).property

theorem rationalLegendre_coefficient_field (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    ((rationalLegendre (p / 6)).coeff n : ZMod p) = (actualLegendreJacobi p).coeff n := by
  have hv := congrArg (fun P : ℚ[X] => P.coeff n) (integralLegendre_value p (p / 6) hp)
  have hr := congrArg (fun P : (ZMod p)[X] => P.coeff n) (integralLegendre_field p hp)
  rw [Polynomial.coeff_map] at hv hr
  rw [← hv]
  exact hr

theorem rationalLegendre_degree (d : ℕ) : (rationalLegendre d).natDegree ≤ d := by
  unfold rationalLegendre
  calc
    _ ≤ ((shiftedLegendre d).map (Int.castRingHom ℚ)).natDegree *
        (C (1 / 2 : ℚ) * (1 - X)).natDegree := Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul
      (Polynomial.natDegree_map_le.trans (by rw [natDegree_shiftedLegendre]))
      jacobiCoordinate_degree
    _ = _ := Nat.mul_one _

theorem rationalLegendre_endpoint_one (d : ℕ) : (rationalLegendre d).eval 1 = 1 := by
  rw [rationalLegendre, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, sub_self, mul_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, coeff_shiftedLegendre]
  simp

/-- The literal low-node quotient is divided in Q before any field residue. -/
noncomputable def lowCarryCoefficient (p n : ℕ) : ℚ :=
  ((rankJacobiNode p 1).coeff n - (rationalLegendre (p / 6)).coeff n) / (p : ℚ)

theorem actual_lowCarryCoefficient_integral (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p (lowCarryCoefficient p n) := by
  have ha := actual_rankJacobiCoefficient_integral p 1 n hp
  have hb := rationalLegendre_coefficient_integral p (p / 6) n hp
  have hf : ((rankJacobiNode p 1).coeff n : ZMod p) =
      ((rationalLegendre (p / 6)).coeff n : ZMod p) := by
    rw [actual_rankJacobiCoefficient_legendre p 1 n hp,
      rationalLegendre_coefficient_field p n hp]
  have hg := (integral_residue_eq_iff p _ _ ha hb).mp hf
  rcases hg with hz | hv
  · simp [lowCarryCoefficient, hz]
  · by_cases hz : (rankJacobiNode p 1).coeff n - (rationalLegendre (p / 6)).coeff n = 0
    · simp [lowCarryCoefficient, hz]
    · have hpq : (p : ℚ) ≠ 0 := by positivity
      rw [lowCarryCoefficient, padicValRat.div hz hpq, padicValRat.self (by omega)]
      omega

noncomputable def lowCarryPolynomial (p : ℕ) : ℚ[X] :=
  WPActualNativeSecondTaylor.coefficientPolynomial (p / 6) (lowCarryCoefficient p)

theorem lowCarryPolynomial_degree (p : ℕ) : (lowCarryPolynomial p).natDegree ≤ p / 6 :=
  WPActualNativeSecondTaylor.coefficientPolynomial_degree _ _

/-- The source is the actual normalized low node, retaining its complete rational lift. -/
theorem actual_lowCarryPolynomial_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankJacobiNode p 1 - rationalLegendre (p / 6) = C (p : ℚ) * lowCarryPolynomial p := by
  have hpq : (p : ℚ) ≠ 0 := by positivity
  ext n
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, lowCarryPolynomial,
    WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  split_ifs with hn
  · unfold lowCarryCoefficient
    field_simp
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((actual_low_rankJacobi_degree p hp).trans_lt (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt
      ((rationalLegendre_degree (p / 6)).trans_lt (by omega))]
    ring

theorem lowCarryPolynomial_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (lowCarryPolynomial p).eval 1 = 0 := by
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (actual_lowCarryPolynomial_source p hp)
  rw [Polynomial.eval_sub, rankJacobiNode_endpoint_one, rationalLegendre_endpoint_one,
    Polynomial.eval_mul, Polynomial.eval_C, sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by positivity)

theorem rankRegular_zero_legendre (d : ℕ) (P : ℚ[X]) :
    rankRegular 0 P = 36 * legendreRegular d P -
      C (5 + 36 * (d : ℚ) * ((d : ℚ) + 1)) * P := by
  simp [rankRegular, legendreRegular, map_mul, map_add, map_ofNat]
  ring

theorem rankJacobiClear_zero_legendre (d : ℕ) (P : ℚ[X]) :
    rankJacobiClear 0 P = 36 * legendreJacobi d P -
      C (5 + 36 * (d : ℚ) * ((d : ℚ) + 1)) * P := by
  simp [rankJacobiClear, legendreJacobi, map_mul, map_add, map_ofNat]
  ring

theorem legendreRegular_jacobi_comp (d : ℕ) (P : ℚ[X]) :
    (legendreRegular d P).comp (C (1 / 2) * (1 - X)) =
      legendreJacobi d (P.comp (C (1 / 2) * (1 - X))) := by
  have h := rankRegular_jacobi_comp 0 P
  rw [rankRegular_zero_legendre d P] at h
  simp only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp] at h
  rw [show (36 : ℚ[X]) = C (36 : ℚ) by rfl, Polynomial.C_comp] at h
  simp only [map_ofNat] at h
  rw [rankJacobiClear_zero_legendre d] at h
  have hs : (36 : ℚ[X]) * (legendreRegular d P).comp (C (1 / 2) * (1 - X)) =
      36 * legendreJacobi d (P.comp (C (1 / 2) * (1 - X))) := by
    linear_combination h
  exact mul_left_cancel₀ (by norm_num : (36 : ℚ[X]) ≠ 0) hs

theorem rationalLegendre_ODE (d : ℕ) : legendreJacobi d (rationalLegendre d) = 0 := by
  have h : legendreRegular d ((shiftedLegendre d).map (Int.castRingHom ℚ)) = 0 := by
    rw [← legendreRegular_map, actual_integer_legendre_ODE, Polynomial.map_zero]
  have hc := congrArg (fun P : ℚ[X] => P.comp (C (1 / 2) * (1 - X))) h
  rw [legendreRegular_jacobi_comp, Polynomial.zero_comp] at hc
  exact hc

theorem legendreJacobi_add {K : Type*} [CommRing K] (d : ℕ) (P Q : K[X]) :
    legendreJacobi d (P + Q) = legendreJacobi d P + legendreJacobi d Q := by
  simp [legendreJacobi, Polynomial.derivative_add]
  ring

theorem legendreJacobi_C_mul {K : Type*} [CommRing K] (d : ℕ) (a : K) (P : K[X]) :
    legendreJacobi d (C a * P) = C a * legendreJacobi d P := by
  simp [legendreJacobi, Polynomial.derivative_mul]
  ring

/-- The full differential source for the actual integral first low-node quotient. -/
theorem actual_lowCarryPolynomial_ODE (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (lowCarryPolynomial p) +
      12 * (X * (rankJacobiNode p 1).derivative -
        C ((p / 6 : ℕ) : ℚ) * rankJacobiNode p 1) = 0 := by
  have hx : rankJacobiNode p 1 = rationalLegendre (p / 6) + C (p : ℚ) * lowCarryPolynomial p := by
    linear_combination actual_lowCarryPolynomial_source p hp
  have hL : legendreJacobi (p / 6) (rankJacobiNode p 1) =
      C (p : ℚ) * legendreJacobi (p / 6) (lowCarryPolynomial p) := by
    rw [hx, legendreJacobi_add, rationalLegendre_ODE, zero_add, legendreJacobi_C_mul]
  have h := actual_low_rankJacobi_ODE p hp
  rw [hL] at h
  have hs : C (p : ℚ) *
      (36 * legendreJacobi (p / 6) (lowCarryPolynomial p) +
        12 * (X * (rankJacobiNode p 1).derivative -
          C ((p / 6 : ℕ) : ℚ) * rankJacobiNode p 1)) = 0 := by
    simp only [map_mul, map_ofNat] at h
    linear_combination h
  exact (mul_eq_zero.mp hs).resolve_left (by simp; positivity)

end WPActualRankTwoFirstLift
