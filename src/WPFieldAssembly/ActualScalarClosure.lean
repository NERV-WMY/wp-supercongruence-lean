import WPFieldAssembly.ActualNC77NativeAttachment
import WPActualFinalConsumer
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open WPPIntegralReduction WPFieldAssembly.ActualNC77NativeAttachment
  WPFieldAssembly.ActualR0Node WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.NativeOriginalResidues

namespace WPFieldAssembly.ActualScalarClosure

variable {K : Type*} [Field K]

/-- The prime-field embedding used for the complete original scalar. -/
noncomputable def scalarMap (p : ℕ) [Fact p.Prime] [CharP K p] : ZMod p →+* K :=
  ZMod.castHom (dvd_refl p) K

theorem scalarMap_injective (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Injective (scalarMap (K := K) p) :=
  (scalarMap (K := K) p).injective

/-- Extension to any characteristic-p field preserves the SAME scalar decision. -/
theorem actual_scalar_iff_mapped_difference_zero
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) ↔
      scalarMap (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) -
        scalarMap (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) = 0 := by
  rw [sub_eq_zero]
  exact (scalarMap_injective (K := K) p).eq_iff.symm

/-- The full arithmetic digit, with the original finite dilogarithm term. -/
noncomputable def originalArithmetic (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  (304 / 3 : K) * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 -
    11 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
      (WPFiniteInversion.integerFermatQuotient p 3 : K) -
    11 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
      (WPFiniteInversion.integerFermatQuotient p 5 : K) -
    9 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
      (WPFiniteInversion.integerFermatQuotient p 5 : K) -
    3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) ^ 2 -
    3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) ^ 2 +
    (5 / 12 : K) * WPFiniteField.R p 16

theorem actualP_transport
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    scalarMap (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) =
      originalArithmetic (K := K) p := by
  rw [actualP_field p hp]
  simp only [scalarMap, originalArithmetic, map_add, map_sub, map_mul,
    map_pow, map_div₀, map_ofNat, map_intCast, ← WPFiniteField.R_castHom]

/-- The original native row, before the joint source evaluation. -/
theorem actual_native_scalar_transport
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    scalarMap (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      2 * scalarMap (K := K) p (residueHom p (integralDeltaUDigit p hp)) -
        scalarMap (K := K) p (originalNorm p : ZMod p) -
        scalarMap (K := K) p (nativeBpair p hp) := by
  rw [actualNC77Scalar_native p hp]
  simp only [map_sub, map_mul, map_ofNat]

/-- All three actual digits and the complete native period remain in this row. -/
noncomputable def originalJoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K :=
  2 * scalarMap (K := K) p (residueHom p (WPFirstResidue.integralActualRho p hp)) +
    (5 / 4 : K) * scalarMap (K := K) p
      (residueHom p (WPMomentPrecision.NativeSecondLift.integralNegativeDigit p hp)) +
    (113 / 28 : K) * scalarMap (K := K) p
      (residueHom p (WPActualPositiveResidueCarry.integralPositiveDigit p hp 1 (by norm_num))) -
    (625 / 216 : K) * scalarMap (K := K) p
      (WPActualEtaIntegration.canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p)

/-- The positive carry cancels the invisible Cp slot before faithful descent. -/
theorem actual_scalar_transport_joint
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    scalarMap (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) =
      originalJoint (K := K) p hp := by
  have h := congrArg (scalarMap (K := K) p)
    (actual_joint_native_scalar_with_positive p hp)
  simp only [map_add, map_sub, map_mul, map_div₀, map_ofNat] at h
  rw [actual_native_scalar_transport p hp]
  exact h.symm

/-- This exact scale-one dictionary uses the actual source digits, not assigned values. -/
theorem actual_scalar_difference_joint
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    scalarMap (K := K) p (WPMomentPrecision.MomentToField.actualNC77Scalar p hp) -
        scalarMap (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) =
      originalJoint (K := K) p hp - originalArithmetic (K := K) p := by
  rw [actual_scalar_transport_joint p hp, actualP_transport p hp]

/-- The faithful field target is exactly the original whole joint row. -/
theorem actual_scalar_iff_original_joint
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp =
        (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) ↔
      originalJoint (K := K) p hp - originalArithmetic (K := K) p = 0 := by
  rw [actual_scalar_iff_mapped_difference_zero (K := K) p hp,
    actual_scalar_difference_joint p hp]

/-- A faithful algebraically closed field supplies the required fifth conic coordinate. -/
theorem exists_faithful_fifth_coordinate (p : ℕ) [Fact p.Prime] :
    ∃ u : AlgebraicClosure (ZMod p), u ^ 2 = 1 / 5 := by
  exact IsAlgClosed.exists_pow_nat_eq (1 / 5 : AlgebraicClosure (ZMod p))
    (by norm_num : 0 < (2 : ℕ))

end WPFieldAssembly.ActualScalarClosure
