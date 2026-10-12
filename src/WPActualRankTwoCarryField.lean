import WPActualRankTwoCarrySource

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoHatLift WPActualRankTwoCarrySource
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoFirstLift
  WPActualRankTwoLowTaylor WPActualRankTwoResidueSource WPActualRankTwoProper
  WPActualRankTwoDividedDifference

namespace WPActualRankTwoCarryField

set_option maxHeartbeats 800000

noncomputable def integralSecondCarry (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[X] :=
  rankCoefficientPolynomial (p + p / 6 - 1)
    (fun n => ⟨actualSecondCarryCoefficient p n, actualSecondCarryCoefficient_integral p n hp⟩)

theorem integralSecondCarry_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralSecondCarry p hp).map (integralRationals p).subtype = actualSecondCarryPolynomial p := by
  ext n
  rw [coeff_map, integralSecondCarry, actualSecondCarryPolynomial, rankCoefficientPolynomial_coeff,
    WPActualNativeSecondTaylor.coefficientPolynomial_coeff]
  split_ifs
  · rfl
  · exact map_zero _

noncomputable def actualSecondCarryField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)[X] :=
  (integralSecondCarry p hp).map (residueHom p)

noncomputable def hatCorrectionPolynomial {K : Type*} [CommRing K]
    (p : ℕ) (Y n : K[X]) : K[X] :=
  -X ^ (p - 1) * Y - 2 * (1 - X ^ 2) * X ^ (p - 1) * n.derivative -
    C ((p : K) - 1) * (1 - X ^ 2) * X ^ (p - 2) * n + 2 * X ^ p * n

noncomputable def carrySourcePolynomial {K : Type*} [CommRing K]
    (p d : ℕ) (s : K) (Y A E R n : K[X]) : K[X] :=
  -C s * (2 * X * A.derivative + A) - Y - C (10 * s) * X * R.derivative +
    C (2 * ((d : K) - 2) * s) * R - hatCorrectionPolynomial p Y n +
    C (p : K) * (2 * X * E.derivative + E + C s * A + C (4 * s) * R) -
    C ((p : K) ^ 2) * E

theorem hatCorrectionPolynomial_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p : ℕ) (Y n : K[X]) :
    (hatCorrectionPolynomial p Y n).map f = hatCorrectionPolynomial p (Y.map f) (n.map f) := by
  simp [hatCorrectionPolynomial, derivative_map]

theorem carrySourcePolynomial_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (p d : ℕ) (s : K) (Y A E R n : K[X]) :
    (carrySourcePolynomial p d s Y A E R n).map f =
      carrySourcePolynomial p d (f s) (Y.map f) (A.map f) (E.map f) (R.map f) (n.map f) := by
  simp [carrySourcePolynomial, hatCorrectionPolynomial_map, derivative_map, map_ofNat]

theorem carrySourcePolynomial_rational (p : ℕ) :
    carrySourcePolynomial p (p / 6) (1 / 6 : ℚ) (rationalLegendre (p / 6))
      (fixedJetJacobi (p / 6)) (fixedErrorJacobi p) (rankDividedJacobi p) (rationalProperJacobi (p / 6)) =
      carryForcing p := by
  have hd : (2 : ℚ) * (((p / 6 : ℕ) : ℚ) - 2) * (1 / 6) = (((p / 6 : ℕ) : ℚ) - 2) / 3 := by ring
  simp only [carrySourcePolynomial, hatCorrectionPolynomial, carryForcing, hatCorrection, hd]
  norm_num

noncomputable def integralCarrySource (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralRationals p)[X] :=
  carrySourcePolynomial p (p / 6) (integralSixth p hp) (integralLegendre p (p / 6) hp)
    (fixedIntegralJetJacobi p hp) (fixedIntegralErrorJacobi p hp)
    (rankDividedIntegralJacobi p hp) (integralProperJacobi p hp)

theorem integralCarrySource_value (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralCarrySource p hp).map (integralRationals p).subtype = carryForcing p := by
  rw [integralCarrySource, carrySourcePolynomial_map, integralLegendre_value,
    fixedIntegralJetJacobi_value, fixedIntegralErrorJacobi_value, rankDividedIntegralJacobi_value,
    integralProperJacobi_value]
  change carrySourcePolynomial p (p / 6) (1 / 6 : ℚ) _ _ _ _ _ = carryForcing p
  exact carrySourcePolynomial_rational p

theorem actualSecondCarryIntegral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (integralSecondCarry p hp) = integralCarrySource p (by omega) := by
  apply polynomial_subtype_injective p
  change (legendreJacobi (p / 6) (integralSecondCarry p hp)).map (integralRationals p).subtype =
    (integralCarrySource p (by omega : 7 ≤ p)).map (integralRationals p).subtype
  rw [legendreJacobi_map, integralSecondCarry_value, integralCarrySource_value]
  exact actualSecondCarryPolynomial_ODE p hp

noncomputable def actualCarryFieldSource (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) : (ZMod p)[X] :=
  -C (1 / 6 : ZMod p) * (2 * X * (actualVariationField p hp).derivative + actualVariationField p hp) -
    actualLegendreJacobi p - C (5 / 3 : ZMod p) * X * (actualRankDividedField p hp).derivative +
    C ((((p / 6 : ℕ) : ZMod p) - 2) / 3) * actualRankDividedField p hp +
    X ^ (p - 1) * actualLegendreJacobi p +
    2 * (1 - X ^ 2) * X ^ (p - 1) * (properLegendreJacobi p).derivative -
    (1 - X ^ 2) * X ^ (p - 2) * properLegendreJacobi p - 2 * X ^ p * properLegendreJacobi p

theorem integralCarrySource_field (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (integralCarrySource p hp).map (residueHom p) = actualCarryFieldSource p hp := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using WPActualGaussProper.small_cast_ne_zero p 3 (by norm_num) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using WPActualGaussProper.small_cast_ne_zero p 6 (by norm_num) (by omega)
  have h53 : (10 : ZMod p) * (1 / 6) = 5 / 3 := by field_simp [h3, h6]; ring
  have hd : (2 : ZMod p) * (((p / 6 : ℕ) : ZMod p) - 2) * (1 / 6) =
      (((p / 6 : ℕ) : ZMod p) - 2) / 3 := by field_simp [h3, h6]; ring
  rw [integralCarrySource, carrySourcePolynomial_map, integralSixth_field,
    integralLegendre_field, integralProperJacobi_field]
  change carrySourcePolynomial p (p / 6) (1 / 6 : ZMod p) (actualLegendreJacobi p)
    (actualVariationField p hp) _ (actualRankDividedField p hp) (properLegendreJacobi p) =
      actualCarryFieldSource p hp
  simp only [carrySourcePolynomial, hatCorrectionPolynomial, actualCarryFieldSource,
    ZMod.natCast_self, h53, hd, zero_pow (by norm_num : 2 ≠ 0), zero_sub,
    map_zero, map_neg, map_one, zero_mul]
  ring

/-- The actual NC80 field equation follows from the literal Q-divided source, retaining all pole terms. -/
theorem actualSecondCarryField_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    legendreJacobi (p / 6) (actualSecondCarryField p hp) = actualCarryFieldSource p (by omega) := by
  have h := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p))
    (actualSecondCarryIntegral_source p hp)
  rw [legendreJacobi_map, integralCarrySource_field] at h
  exact h

theorem actualSecondCarryField_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualSecondCarryField p hp).natDegree ≤ p + p / 6 - 1 :=
  Polynomial.natDegree_map_le.trans (rankCoefficientPolynomial_degree _ _)

end WPActualRankTwoCarryField
