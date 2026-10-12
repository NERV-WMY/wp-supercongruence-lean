import WPActualNativeDegree
import WPActualPositivePair
import WPMomentPrecision.Conic.WPRamifiedRegularResonance
import Mathlib.RingTheory.LaurentSeries

open scoped Polynomial PowerSeries LaurentSeries
open Polynomial WPActualNativeHasse WPActualNativeDegree WPActualRankTwoLegendreField
  WPActualPositivePair WPRamifiedRegularResonance

namespace WPActualConicInfinitySource

/-- The original native Euler primitive, retaining every coefficient up to d. -/
noncomputable def nativeHField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  eulerPrimitive p (nativeField p (p / 6))

theorem nativeHField_coeff (p n : ℕ) [Fact p.Prime] :
    (nativeHField p).coeff n =
      (if n ≤ p / 6 then (WPReview.nativeCoefficient n : ZMod p) else 0) / (n : ZMod p) := by
  rw [nativeHField, eulerPrimitive_coeff, nativeField_coeff]
  simp only [Nat.lt_succ_iff]

theorem nativeHField_degree (p : ℕ) [Fact p.Prime] :
    (nativeHField p).natDegree ≤ p / 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeHField_coeff, if_neg (by omega), zero_div]

theorem nativeHField_origin (p : ℕ) [Fact p.Prime] : (nativeHField p).coeff 0 = 0 := by
  rw [nativeHField_coeff]
  simp

noncomputable def rankDensityNumerator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (nativeHField p).comp (1 - X ^ 2)

noncomputable def rankDensityDenominator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (1 - X ^ 2) * actualLegendreJacobi p ^ 2

theorem rankDensityNumerator_degree (p : ℕ) [Fact p.Prime] :
    (rankDensityNumerator p).natDegree ≤ 2 * (p / 6) := by
  have hg : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
  have hd : (rankDensityNumerator p).natDegree ≤
      (nativeHField p).natDegree * (1 - X ^ 2 : (ZMod p)[X]).natDegree := natDegree_comp_le
  exact hd.trans (by nlinarith [nativeHField_degree p])

theorem rankDensityDenominator_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (rankDensityDenominator p).natDegree = 2 * (p / 6) + 2 := by
  have hg : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by compute_degree; norm_num
  have hg0 : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hg
    omega
  have hY : actualLegendreJacobi p ≠ 0 := by
    intro hz
    have hd := actualLegendreJacobi_exact_degree p hp
    rw [hz, natDegree_zero] at hd
    omega
  rw [rankDensityDenominator, natDegree_mul hg0 (pow_ne_zero 2 hY), natDegree_pow,
    actualLegendreJacobi_exact_degree p hp, hg]
  omega

theorem rankDensityDenominator_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankDensityDenominator p ≠ 0 := by
  intro hz
  have hd := rankDensityDenominator_degree p hp
  rw [hz, natDegree_zero] at hd
  omega

/-- The complete reciprocal density is a power series because its denominator is a unit. -/
noncomputable def rankInfinitySeries (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ :=
  -(((rankDensityNumerator p).reflect (2 * (p / 6)) : (ZMod p)⟦X⟧) *
    ((rankDensityDenominator p).reflect (2 * (p / 6) + 2) : (ZMod p)⟦X⟧)⁻¹)

theorem rankInfinityDenominator_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff
      ((rankDensityDenominator p).reflect (2 * (p / 6) + 2) : (ZMod p)⟦X⟧) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, ← rankDensityDenominator_degree p hp,
    ← Polynomial.reverse, coeff_zero_reverse]
  exact leadingCoeff_ne_zero.mpr (rankDensityDenominator_ne_zero p hp)

theorem rankInfinitySeries_cleared (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    rankInfinitySeries p *
        ((rankDensityDenominator p).reflect (2 * (p / 6) + 2) : (ZMod p)⟦X⟧) =
      -((rankDensityNumerator p).reflect (2 * (p / 6)) : (ZMod p)⟦X⟧) := by
  rw [rankInfinitySeries]
  rw [neg_mul, mul_assoc, PowerSeries.inv_mul_cancel _ (rankInfinityDenominator_unit p hp),
    mul_one]

/-- The actual native density has zero first resonance after the literal cubic conic substitution. -/
theorem actual_rank_conic_resonance_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.coeff (p - 1)
      ((rankInfinitySeries p).subst (conicInfinitySeries p) *
        PowerSeries.derivative (ZMod p) (conicInfinitySeries p)) = 0 :=
  actual_conic_resonance_zero p hp (rankInfinitySeries p)

end WPActualConicInfinitySource
