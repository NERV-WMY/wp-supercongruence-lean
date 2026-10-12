import WPActualRankTwoLowTaylor

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoParameter
  WPActualRankTwoDividedDifference WPActualRankTwoGaussODE
  WPActualRankTwoLegendreField WPActualRankTwoLowTaylor

namespace WPActualRankTwoResidueSource

set_option maxHeartbeats 800000

/-- The original two-node divided polynomial in its proved integral coefficient model. -/
noncomputable def rankDividedIntegralPolynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p - 1 - p / 6)
    (fun n => if hn : n < p then
      ⟨rankDividedCoefficient p n, actual_rankDividedCoefficient_integral p n hp hn⟩ else 0)

theorem rankDividedIntegralPolynomial_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankDividedIntegralPolynomial p hp).map (integralRationals p).subtype =
      rankDividedPolynomial p := by
  ext n
  rw [Polynomial.coeff_map, rankDividedIntegralPolynomial, rankDividedPolynomial,
    rankCoefficientPolynomial_coeff, WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  by_cases hn : n < p - 1 - p / 6 + 1
  · rw [if_pos hn, if_pos hn, dif_pos (by omega)]
    rfl
  · simp [hn]

noncomputable def rankDividedIntegralJacobi (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  (rankDividedIntegralPolynomial p hp).comp (C (integralHalf p hp) * (1 - X))

theorem rankDividedIntegralJacobi_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankDividedIntegralJacobi p hp).map (integralRationals p).subtype = rankDividedJacobi p := by
  rw [rankDividedIntegralJacobi, Polynomial.map_comp, rankDividedIntegralPolynomial_value]
  simp [rankDividedJacobi, Polynomial.map_mul, Polynomial.map_sub, integralHalf]

theorem actual_rankDividedJacobi_integral (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    0 ≤ padicValRat p ((rankDividedJacobi p).coeff n) := by
  rw [← rankDividedIntegralJacobi_value p hp, Polynomial.coeff_map]
  exact ((rankDividedIntegralJacobi p hp).coeff n).property

theorem rankDividedIntegralJacobi_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankDividedIntegralJacobi p hp).natDegree ≤ p - 1 - p / 6 := by
  unfold rankDividedIntegralJacobi
  have hcoordinate : (C (integralHalf p hp) * (1 - X)).natDegree ≤ 1 := by compute_degree
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul (rankCoefficientPolynomial_degree _ _) hcoordinate).trans (by simp))

theorem rankDividedIntegralJacobi_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankDividedIntegralJacobi p hp).eval 1 = 0 := by
  apply Subtype.ext
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (rankDividedIntegralJacobi_value p hp)
  rw [rankDividedJacobi_endpoint_one] at h
  change ((rankDividedIntegralJacobi p hp).map (integralRationals p).subtype).eval
    ((integralRationals p).subtype 1) = 0 at h
  rw [Polynomial.eval_map_apply] at h
  exact h

noncomputable def dividedSource {K : Type*} [CommRing K]
    (d p : ℕ) (P Q : K[X]) : K[X] :=
  36 * legendreJacobi d P + C (12 * (p : K)) * (X * P.derivative - C (d : K) * P) -
    36 * (2 * X * Q.derivative + C (1 - (p : K)) * Q)

theorem dividedSource_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (d p : ℕ) (P Q : K[X]) :
    (dividedSource d p P Q).map f = dividedSource d p (P.map f) (Q.map f) := by
  simp [dividedSource, legendreJacobi_map, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.derivative_map, map_ofNat]

/-- Exact rational source, before taking any field residue or discarding a p term. -/
theorem actual_rankDividedJacobi_legendre_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (rankDividedJacobi p) +
      C (12 * (p : ℚ)) * (X * (rankDividedJacobi p).derivative -
        C ((p / 6 : ℕ) : ℚ) * rankDividedJacobi p) =
      36 * (2 * X * (rankJacobiNode p 5).derivative +
        C (1 - (p : ℚ)) * rankJacobiNode p 5) := by
  rw [← actual_low_rankJacobi_operator p hp]
  exact actual_rankDividedJacobi_ODE p hp

theorem actual_rankDividedIntegralJacobi_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    36 * legendreJacobi (p / 6) (rankDividedIntegralJacobi p hp) +
      C (12 * (p : integralRationals p)) *
        (X * (rankDividedIntegralJacobi p hp).derivative -
          C ((p / 6 : ℕ) : integralRationals p) * rankDividedIntegralJacobi p hp) =
      36 * (2 * X * (rankIntegralJacobi p hp 5).derivative +
        C (1 - (p : integralRationals p)) * rankIntegralJacobi p hp 5) := by
  apply sub_eq_zero.mp
  apply polynomial_subtype_injective p
  change (dividedSource (p / 6) p (rankDividedIntegralJacobi p hp)
    (rankIntegralJacobi p hp 5)).map (integralRationals p).subtype =
    (0 : (integralRationals p)[X]).map (integralRationals p).subtype
  rw [dividedSource_map, rankDividedIntegralJacobi_value, rankIntegralJacobi_value,
    Polynomial.map_zero]
  exact sub_eq_zero.mpr (actual_rankDividedJacobi_legendre_source p hp)

noncomputable def actualRankDividedField (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (ZMod p)[X] :=
  (rankDividedIntegralJacobi p hp).map (residueHom p)

theorem actualRankDividedField_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualRankDividedField p hp).natDegree ≤ p - 1 - p / 6 :=
  Polynomial.natDegree_map_le.trans (rankDividedIntegralJacobi_degree p hp)

theorem actualRankDividedField_endpoint_one (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (actualRankDividedField p hp).eval 1 = 0 := by
  unfold actualRankDividedField
  rw [← (residueHom p).map_one, Polynomial.eval_map_apply,
    rankDividedIntegralJacobi_endpoint_one, map_zero]

/-- The actual divided field polynomial has the complete forced Legendre source. -/
theorem actualRankDividedField_source (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    legendreJacobi (p / 6) (actualRankDividedField p hp) =
      2 * X * (actualLegendreJacobi p).derivative + actualLegendreJacobi p := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (sub_eq_zero.mpr (actual_rankDividedIntegralJacobi_source p hp))
  change (dividedSource (p / 6) p (rankDividedIntegralJacobi p hp)
    (rankIntegralJacobi p hp 5)).map (residueHom p) =
    (0 : (integralRationals p)[X]).map (residueHom p) at h
  rw [dividedSource_map, rankIntegralJacobi_field, Polynomial.map_zero] at h
  dsimp only [dividedSource] at h
  simp only [ZMod.natCast_self, mul_zero, sub_zero, Polynomial.C_0, Polynomial.C_1,
    zero_mul, add_zero, one_mul] at h
  have h36 : (36 : ZMod p) ≠ 0 := by
    have hd := WPActualRankTwoParameter.rankDenominator_origin_residue_ne_zero p 1 hp (by omega)
    simpa [WPActualRankTwoParameter.rankDenominator_eval_zero] using hd
  have h36poly : (36 : (ZMod p)[X]) ≠ 0 := by
    rw [show (36 : (ZMod p)[X]) = C (36 : ZMod p) by rfl]
    exact Polynomial.C_ne_zero.mpr h36
  exact mul_left_cancel₀ h36poly (sub_eq_zero.mp h)

end WPActualRankTwoResidueSource
