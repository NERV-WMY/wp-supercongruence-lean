import WPFirstResidue.RankDensity.Local
import WPMomentPrecision.Conic.WPActualConicWeightedResidue

open scoped Polynomial PowerSeries LaurentSeries RatFunc
open Polynomial WPActualConicInfinitySource WPActualConicInfinityAttachment
  WPRamifiedRegularResonance WPRationalInfinitySeries WPActualConicWeightedResidue
  WPMomentPrecision.ConicCoordinates

namespace WPFirstResidue.ConicRankDensity

/-- The original omega_H pulls back to the complete cubic rank series with its factor 1/3. -/
theorem actual_omega_complete_local_density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((PowerSeries.C (1 / 3) *
        ((rankInfinitySeries p).subst (conicInfinitySeries p) *
          PowerSeries.derivative (ZMod p) (conicInfinitySeries p)) :
        (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      -((conicLocalVariable p)⁻¹) ^ 2 *
        nativeOmegaDensity p (algebraMap (ZMod p) (ZMod p)⸨X⸩)
          (conicLocalVariable p)⁻¹ := by
  have h3field : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h3 : (3 : (ZMod p)⸨X⸩) ≠ 0 := by
    simpa only [map_ofNat] using
      (map_ne_zero (algebraMap (ZMod p) (ZMod p)⸨X⸩)).mpr h3field
  have hs := conicInfinitySeries_ne_zero p hp
  have hr := actual_rank_substituted_representation p hp (conicInfinitySeries p)
    (conicInfinitySeries_hasSubst p) (conicInfinitySeries_origin p) hs
  have hj := conicInfinitySeries_signed_jacobian p hp
  have ho := actual_omega_rank_density p hp
    (algebraMap (ZMod p) (ZMod p)⸨X⸩) (conicLocalVariable p)⁻¹ h3
  have harg := congrArg
    (nativeRankDensity p (algebraMap (ZMod p) (ZMod p)⸨X⸩))
    (conicInfinitySeries_inverse p hp)
  rw [PowerSeries.coe_mul, PowerSeries.coe_mul, PowerSeries.coe_C,
    ← coefficient_algebraMap_laurent, map_div₀, map_one, map_ofNat, hr, hj,
    harg]
  calc
    _ = -((conicLocalVariable p)⁻¹) ^ 2 *
        ((1 / 3) * nativeRankDensity p (algebraMap (ZMod p) (ZMod p)⸨X⸩)
          (cubic (conicLocalVariable p)⁻¹) *
          (3 * (4 * ((conicLocalVariable p)⁻¹) ^ 2 - 1))) := by
      field_simp [hs]
    _ = _ := by rw [← ho]

/-- The signed reciprocal expansion is the expansion of the original rational omega_H. -/
theorem actual_rational_omega_source_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ (actualOmegaHInfinityRational p) =
      ((PowerSeries.C (1 / 3) *
        ((rankInfinitySeries p).subst (conicInfinitySeries p) *
          PowerSeries.derivative (ZMod p) (conicInfinitySeries p)) :
        (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) := by
  have hX : algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ RatFunc.X =
      conicLocalVariable p := by
    simpa only [conicLocalVariable, PowerSeries.coe_X] using
      (RatFunc.coe_X (F := ZMod p))
  have hf : (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩).comp RatFunc.C =
      algebraMap (ZMod p) (ZMod p)⸨X⸩ := rational_coefficient_hom_laurent
  rw [actual_omega_complete_local_density p hp]
  simp only [actualOmegaHInfinityRational, map_mul, map_neg, map_pow, map_inv₀,
    map_nativeOmegaDensity, hf, hX]

theorem conic_L_denominator_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    PowerSeries.constantCoeff (5 - PowerSeries.X ^ 2 : (ZMod p)⟦X⟧) ≠ 0 := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  simpa [map_ofNat] using h5

/-- The Frobenius weight retains the entire reciprocal rational L, not only its leading term. -/
theorem conicLUnit_laurent (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((conicLUnit p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) =
      (3 * conicLocalVariable p ^ 2 - 11) / (5 - conicLocalVariable p ^ 2) := by
  rw [conicLUnit, PowerSeries.coe_mul,
    powerSeries_inverse_cast _ (conic_L_denominator_unit p hp)]
  simp only [PowerSeries.coe_sub, PowerSeries.coe_mul, PowerSeries.coe_pow,
    map_ofNat, div_eq_mul_inv, conicLocalVariable]

theorem conic_L_denominator_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    5 - conicLocalVariable p ^ 2 ≠ 0 := by
  intro he
  have hcast : (((5 - PowerSeries.X ^ 2 : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩)) =
      5 - conicLocalVariable p ^ 2 := by
    simp only [PowerSeries.coe_sub, PowerSeries.coe_pow, map_ofNat, conicLocalVariable]
  rw [← hcast] at he
  have hc := congrArg (fun F : (ZMod p)⸨X⸩ => F.coeff 0) he
  rw [PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, HahnSeries.coeff_zero] at hc
  exact conic_L_denominator_unit p hp hc

theorem actual_L_complete_unit (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    L (conicLocalVariable p)⁻¹ =
      (conicLocalVariable p)⁻¹ *
        ((conicLUnit p : (ZMod p)⟦X⟧) : (ZMod p)⸨X⸩) := by
  rw [conicLUnit_laurent p hp]
  unfold L
  field_simp [conicLocalVariable_ne_zero p, conic_L_denominator_ne_zero p hp]

theorem conic_weight_shift (p : ℕ) [Fact p.Prime] :
    HahnSeries.single (-(p : ℤ)) (1 : ZMod p) = ((conicLocalVariable p)⁻¹) ^ p := by
  simpa only [conicLocalVariable, PowerSeries.coe_X, zpow_neg, zpow_natCast, inv_pow] using
    (RatFunc.single_zpow (F := ZMod p) (-(p : ℤ)))

/-- Equality of the actual rational weighted differential and the retained complete local density. -/
theorem actual_native_weighted_infinity_density (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualConicWeightedDensity p =
      L (conicLocalVariable p)⁻¹ ^ p *
        (-((conicLocalVariable p)⁻¹) ^ 2 *
          nativeOmegaDensity p (algebraMap (ZMod p) (ZMod p)⸨X⸩)
            (conicLocalVariable p)⁻¹) := by
  rw [actualConicWeightedDensity, PowerSeries.coe_mul, PowerSeries.coe_pow,
    actual_omega_complete_local_density p hp, conic_weight_shift, actual_L_complete_unit p hp,
    mul_pow]
  ring

noncomputable def actualWeightedOmegaHInfinityRational (p : ℕ) [Fact p.Prime] :
    RatFunc (ZMod p) :=
  L (RatFunc.X : RatFunc (ZMod p))⁻¹ ^ p * actualOmegaHInfinityRational p

/-- Source attachment in RatFunc, including the full signed reciprocal and cubic substitutions. -/
theorem actual_rational_weighted_source_attachment (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
      (actualWeightedOmegaHInfinityRational p) = actualConicWeightedDensity p := by
  have hX : algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩ RatFunc.X =
      conicLocalVariable p := by
    simpa only [conicLocalVariable, PowerSeries.coe_X] using
      (RatFunc.coe_X (F := ZMod p))
  have hf : (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩).comp RatFunc.C =
      algebraMap (ZMod p) (ZMod p)⸨X⸩ := rational_coefficient_hom_laurent
  rw [actual_native_weighted_infinity_density p hp]
  simp only [actualWeightedOmegaHInfinityRational, actualOmegaHInfinityRational,
    map_mul, map_pow, map_neg, map_inv₀, map_nativeOmegaDensity, hf, hX,
    L, map_div₀, map_sub, map_one, map_ofNat]

/-- The residue is now the residue of the actual rational source, with no residue-equality premise. -/
theorem actual_rational_weighted_infinity_residue_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (algebraMap (RatFunc (ZMod p)) (ZMod p)⸨X⸩
      (actualWeightedOmegaHInfinityRational p)).coeff (-1) = 0 := by
  rw [actual_rational_weighted_source_attachment p hp]
  exact actual_conic_weighted_residue_zero p hp

end WPFirstResidue.ConicRankDensity
