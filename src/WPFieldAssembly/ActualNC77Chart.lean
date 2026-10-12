import WPFieldAssembly.NativeQuadraticInverse
import WPMomentPrecision.NativeSecondLift

open scoped Polynomial
open Polynomial WPPIntegralReduction
  WPActualRankTwoParameter WPActualRankTwoLegendreField
  WPActualRankTwoResidueSource WPActualNativeJacobiJet WPActualNativeJetODE
  WPFieldAssembly.NativeQuadraticInverse
  WPMomentPrecision.NativeSecondLift

namespace WPFieldAssembly.ActualNC77Chart

variable (p : ℕ) [Fact p.Prime]

theorem contract_C_mul {R : Type*} [CommRing R] (a : R) (P : R[X]) :
    contract 2 (C a * P) = C a * contract 2 P := by
  ext n
  simp only [coeff_contract (by norm_num : (2 : ℕ) ≠ 0), coeff_C_mul]

theorem quadraticInverse_C_mul {R : Type*} [CommRing R] (a : R) (P : R[X]) :
    quadraticInverse (C a * P) = C a * quadraticInverse P := by
  rw [quadraticInverse, contract_C_mul, mul_comp, C_comp]
  rfl

noncomputable def mixedQ : ℚ[X] :=
  quadraticInverse (rankJacobiNode p 1 * actualU p)

noncomputable def normQ : ℚ[X] :=
  quadraticInverse (actualU p ^ 2)

noncomputable def integralMixedQ (hp : 7 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (rankIntegralJacobi p hp 1 * integralU p hp)

noncomputable def integralNormQ (hp : 7 ≤ p) : (integralRationals p)[X] :=
  quadraticInverse (integralU p hp ^ 2)

theorem integralMixedQ_value (hp : 7 ≤ p) :
    (integralMixedQ p hp).map (integralRationals p).subtype = mixedQ p := by
  rw [integralMixedQ, quadraticInverse_map, Polynomial.map_mul,
    rankIntegralJacobi_value, integralU_value]
  rfl

theorem integralNormQ_value (hp : 7 ≤ p) :
    (integralNormQ p hp).map (integralRationals p).subtype = normQ p := by
  rw [integralNormQ, quadraticInverse_map, Polynomial.map_pow, integralU_value]
  rfl

theorem integralMixedQ_field (hp : 7 ≤ p) :
    (integralMixedQ p hp).map (residueHom p) =
      quadraticInverse (actualLegendreJacobi p * actualUField p hp) := by
  rw [integralMixedQ, quadraticInverse_map, Polynomial.map_mul,
    rankIntegralJacobi_field]
  rfl

theorem integralNormQ_field (hp : 7 ≤ p) :
    (integralNormQ p hp).map (residueHom p) =
      quadraticInverse (actualUField p hp ^ 2) := by
  rw [integralNormQ, quadraticInverse_map, Polynomial.map_pow]
  rfl

/-- The whole actual mixed q-polynomial is the original native jet divided by 12. -/
theorem actual_mixed_field_source (hp : 19 ≤ p) :
    12 * (integralMixedQ p (by omega)).map (residueHom p) = nativeJetField p := by
  have h := congrArg
    (fun P : (ZMod p)[X] => quadraticInverse P)
    (actual_native_jet_twelve_YU p hp)
  rw [nativeJacobiJet, quadraticInverse_quadratic] at h
  have hc :
      12 * actualLegendreJacobi p * actualUField p (by omega) =
        C (12 : ZMod p) *
          (actualLegendreJacobi p * actualUField p (by omega)) := by
    simp only [map_ofNat]
    ring
  rw [hc, quadraticInverse_C_mul] at h
  rw [integralMixedQ_field]
  simpa only [map_ofNat] using h.symm

/-- This field transport removes no coefficient band of the actual norm. -/
theorem actual_norm_field_source (hp : 7 ≤ p) :
    (integralNormQ p hp).map (residueHom p) =
      quadraticInverse
        ((C (1 / 6 : ZMod p) * actualRankDividedField p hp) ^ 2) := by
  rw [integralNormQ_field, actual_U_field]

theorem actual_mixed_integral (hp : 7 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((mixedQ p).coeff n) := by
  rw [← integralMixedQ_value p hp, coeff_map]
  exact ((integralMixedQ p hp).coeff n).property

theorem actual_norm_integral (hp : 7 ≤ p) (n : ℕ) :
    0 ≤ padicValRat p ((normQ p).coeff n) := by
  rw [← integralNormQ_value p hp, coeff_map]
  exact ((integralNormQ p hp).coeff n).property

end WPFieldAssembly.ActualNC77Chart
