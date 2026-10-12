import WPFieldAssembly.ActualJointGreen
import WPFieldAssembly.ActualGreenPrimitive
import WPFieldAssembly.ActualCauchyTbarAttachment
import WPFieldAssembly.ActualEtaTransport
import WPFieldAssembly.NativeStrictTail
import WPFieldAssembly.ActualNormCrossAttachment
import WPFieldAssembly.ActualConicFiniteLog
import WPFiniteZSource
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.ActualBalancedTrace

section LogReflection
variable {K : Type*} [Field K]

private theorem LPscaled_laurent (p : ℕ) (c : K) :
    ((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c * X)).toLaurent =
      ∑ j ∈ Finset.Ico 1 p, LaurentPolynomial.C (c ^ j / (j : K)) * T (j : ℤ) := by
  unfold WPFiniteAffineLog.LP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, map_sum,
    map_mul, map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow, mul_one,
    ← mul_assoc, ← map_mul]
  congr 2
  simp only [div_eq_mul_inv]
  ring

/-- Inversion of the entire literal logarithm, including every cutoff coefficient. -/
theorem LPscaled_inversion (p : ℕ) [Fact p.Prime] [CharP K p] (c : K) (hc : c ≠ 0) :
    invert (((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c * X)).toLaurent) =
      -LaurentPolynomial.C (c ^ p) * T (-(p : ℤ)) *
        ((WPFiniteAffineLog.LP p).comp (Polynomial.C c⁻¹ * X)).toLaurent := by
  rw [LPscaled_laurent, map_sum]
  simp only [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => LaurentPolynomial.C (c ^ j / (j : K)) * T (-(j : ℤ))),
    LPscaled_laurent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Ico.mp hj
  have hpow : c ^ (p - j) = c ^ p * (c⁻¹) ^ j := by
    rw [pow_sub₀ c hc (by omega : j ≤ p), inv_pow]
  have hden := WPFiniteField.reflected_denominator (K := K) p j hj
  have hcq : c ^ (p - j) / ((p - j : ℕ) : K) = -(c ^ p) * ((c⁻¹) ^ j / (j : K)) := by
    rw [hpow, hden]
    simp only [div_eq_mul_inv, inv_neg]
    ring
  have hT : (T (-(p : ℤ)) : K[T;T⁻¹]) * T (j : ℤ) = T (-((p - j : ℕ) : ℤ)) := by
    rw [← T_add]
    congr 1
    omega
  rw [hcq]
  simp only [map_mul, map_neg]
  linear_combination
    (LaurentPolynomial.C (c ^ p) * LaurentPolynomial.C ((c⁻¹) ^ j / (j : K))) * hT

/-- The original positive and negative log rows exchange, with the same p phase. -/
theorem actual_log_rows_inversion (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent =
      -T (-(p : ℤ)) * (WPFinitePSource.logDifference p : K[X]).toLaurent ∧
    invert (WPFinitePSource.logDifference p : K[X]).toLaurent =
      -T (-(p : ℤ)) * (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hqp : (1 / 4 : K) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hi4 := LPscaled_inversion (K := K) p 4 h4
  have hiq := LPscaled_inversion (K := K) p (1 / 4) (one_div_ne_zero h4)
  rw [h4p] at hi4
  rw [hqp, one_div, inv_inv] at hiq
  have hC4 : LaurentPolynomial.C ((4 : K)⁻¹) * LaurentPolynomial.C (4 : K) =
      (1 : K[T;T⁻¹]) := by
    rw [← map_mul, inv_mul_cancel₀ h4, map_one]
  constructor
  · simp only [WPFiniteABSourceTail.logTrace, WPFinitePSource.logDifference,
      map_add, map_sub, map_neg, map_mul, Polynomial.toLaurent_C,
      LaurentPolynomial.invert_C, hi4, hiq, one_div]
    rw [mul_comm (Polynomial.C (4 : K)) X]
    calc
      _ = (LaurentPolynomial.C ((4 : K)⁻¹) * LaurentPolynomial.C (4 : K)) *
          T (-(p : ℤ)) *
          (((WPFiniteAffineLog.LP p : K[X]).comp
              (Polynomial.C ((4 : K)⁻¹) * X)).toLaurent -
            ((WPFiniteAffineLog.LP p : K[X]).comp (X * Polynomial.C (4 : K))).toLaurent) := by
        ring
      _ = T (-(p : ℤ)) *
          (((WPFiniteAffineLog.LP p : K[X]).comp
              (Polynomial.C ((4 : K)⁻¹) * X)).toLaurent -
            ((WPFiniteAffineLog.LP p : K[X]).comp (X * Polynomial.C (4 : K))).toLaurent) := by
        rw [hC4, one_mul]
      _ = _ := by ring
  · simp only [WPFiniteABSourceTail.logTrace, WPFinitePSource.logDifference,
      map_add, map_sub, map_neg, map_mul, Polynomial.toLaurent_C,
      hi4, hiq, one_div]
    ring
end LogReflection

section ComparisonField
variable {K : Type*} [Field K]

noncomputable def movingEvenField (p : ℕ) : K[X] :=
  (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate
noncomputable def comparisonField (p : ℕ) : K[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 15 : K) * WPFiniteZSource.phase p *
    ((movingEvenField p).toLaurent + invert (movingEvenField p).toLaurent)

/-- All logarithm rows cancel under the literal cutoff reflection. -/
theorem P_symmetric_W (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u) =
      LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p)) * WPFiniteZSource.phase p *
        ((WPFiniteWSource.W p : K[X]).toLaurent + invert (WPFiniteWSource.W p : K[X]).toLaurent +
          LaurentPolynomial.C (4 * WPFiniteABSourceTail.epsilon p * WPFifthEntropy.C p u / 15)) := by
  have h2 : (2 : K) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      WPFiniteField.denominator_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero (K := K) p 5 (Finset.mem_Ico.mpr (by omega)))
  have hlog := actual_log_rows_inversion (K := K) p hp
  have h2eps : (2 * WPFiniteABSourceTail.epsilon p : K) ≠ 0 := mul_ne_zero h2 heps
  have hone : (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      (2 * WPFiniteABSourceTail.epsilon p) = 1 := one_div_mul_cancel h2eps
  have hT : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hc2 : LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p : K) =
      4 * LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) := by
    change LaurentPolynomial.C (2 / WPFiniteABSourceTail.epsilon p : K) =
      LaurentPolynomial.C 4 * LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K)
    rw [← map_mul]
    congr 1
    rw [mul_one_div]
    apply (div_eq_div_iff heps h2eps).2
    ring
  have hc17 : LaurentPolynomial.C (17 / (2 * WPFiniteABSourceTail.epsilon p) : K) =
      17 * LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) := by
    change LaurentPolynomial.C (17 / (2 * WPFiniteABSourceTail.epsilon p) : K) =
      LaurentPolynomial.C 17 * LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K)
    rw [← map_mul]
    congr 1
    ring
  have hce : LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      LaurentPolynomial.C (4 * WPFiniteABSourceTail.epsilon p * WPFifthEntropy.C p u / 15) =
        LaurentPolynomial.C (2 * WPFifthEntropy.C p u / 15) := by
    rw [← map_mul]
    congr 1
    linear_combination (2 * WPFifthEntropy.C p u / 15) * hone
  have hsplit : LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      WPFiniteZSource.phase p * ((WPFiniteWSource.W p : K[X]).toLaurent +
        invert (WPFiniteWSource.W p : K[X]).toLaurent +
          LaurentPolynomial.C (4 * WPFiniteABSourceTail.epsilon p * WPFifthEntropy.C p u / 15)) =
      LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) * WPFiniteZSource.phase p *
        ((WPFiniteWSource.W p : K[X]).toLaurent + invert (WPFiniteWSource.W p : K[X]).toLaurent) +
      LaurentPolynomial.C (2 * WPFifthEntropy.C p u / 15) * WPFiniteZSource.phase p := by
    linear_combination WPFiniteZSource.phase p * hce
  rw [hsplit]
  unfold WPFiniteZSource.P WPFiniteABSourceTail.A WPFiniteABSourceTail.uSlot
    WPFiniteABSourceTail.B0 WPFiniteABSourceTail.Bpoly WPFinitePSource.Cminus WPFiniteZSource.phase
  simp only [map_add, map_sub, map_mul, Polynomial.toLaurent_C,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, neg_neg, hlog.1, hlog.2, hc2, hc17]
  simp only [div_eq_mul_inv, map_mul, map_add, map_sub, map_neg, map_ofNat, map_one] at *
  linear_combination -(2 * LaurentPolynomial.C (15⁻¹ : K)) *
    (WPFiniteABSourceTail.logTrace p : K[X]).toLaurent * hT

/-- The actual fifth offset cancels before forming the reflection numerator. -/
theorem actual_P_symmetric_comparison (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteZSource.P p u + invert (WPFiniteZSource.P p u) = comparisonField (K := K) p := by
  rw [P_symmetric_W p hp u]
  have h2 : (2 : K) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using
      WPFiniteField.denominator_ne_zero (K := K) p 2 (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : K) ≠ 0 := pow_ne_zero _
    (WPFiniteField.denominator_ne_zero (K := K) p 5 (Finset.mem_Ico.mpr (by omega)))
  have hC := WPFiniteWSource.deltaE_fifth (K := K) p hp u hu
  have hone : (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      (2 * WPFiniteABSourceTail.epsilon p) = 1 :=
    one_div_mul_cancel (mul_ne_zero h2 heps)
  have hW : (WPFiniteWSource.W p : K[X]).toLaurent + invert (WPFiniteWSource.W p : K[X]).toLaurent +
      LaurentPolynomial.C (4 * WPFiniteABSourceTail.epsilon p * WPFifthEntropy.C p u / 15) =
        LaurentPolynomial.C (2 * WPFiniteABSourceTail.epsilon p / 15) *
          ((movingEvenField p : K[X]).toLaurent + invert (movingEvenField p : K[X]).toLaurent) := by
    simp only [WPFiniteWSource.W, map_mul, map_sub, Polynomial.toLaurent_C,
      LaurentPolynomial.invert_C, hC, movingEvenField]
    simp only [div_eq_mul_inv, map_mul, map_ofNat]
    ring
  have hs : LaurentPolynomial.C (1 / (2 * WPFiniteABSourceTail.epsilon p) : K) *
      LaurentPolynomial.C (2 * WPFiniteABSourceTail.epsilon p / 15) = LaurentPolynomial.C (1 / 15 : K) := by
    rw [← map_mul]
    congr 1
    linear_combination (1 / 15 : K) * hone
  rw [hW]
  unfold comparisonField
  linear_combination WPFiniteZSource.phase p *
    ((movingEvenField p : K[X]).toLaurent + invert (movingEvenField p : K[X]).toLaurent) * hs
end ComparisonField

variable (p : ℕ) [Fact p.Prime]

noncomputable def comparisonCoordinateI : (WPPIntegralReduction.integralRationals p)[X] :=
  Polynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 5) * (X + 1)

noncomputable def movingEvenIntegral : (WPPIntegralReduction.integralRationals p)[X] :=
  (ActualJointGreen.finiteEvenSquaredIntegral p).comp (4 * comparisonCoordinateI p) -
    (ActualJointGreen.finiteEvenSquaredIntegral p).comp (comparisonCoordinateI p)

noncomputable def comparisonEndIntegral : WPPIntegralReduction.integralRationals p :=
  (ActualJointGreen.finiteEvenSquaredIntegral p).eval (WPActualRankTwoHatLift.smallIntegralInverse p 4) -
    (ActualJointGreen.finiteEvenSquaredIntegral p).eval 4

noncomputable def comparisonPhaseIntegral : (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  17 - 4 * T (p : ℤ) - 4 * T (-(p : ℤ))

noncomputable def comparisonIntegral : (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 15) * comparisonPhaseIntegral p *
    ((movingEvenIntegral p).toLaurent + invert (movingEvenIntegral p).toLaurent) +
    LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 15 *
      (17 - 4 * ((WPActualRankTwoHatLift.smallIntegralInverse p 4) ^ p + 4 ^ p)) * comparisonEndIntegral p)

noncomputable def comparisonRational (_hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype (comparisonIntegral p)

private theorem evenSquared_scaled_difference {K : Type*} [Field K] (p : ℕ) :
    (WPFiniteLVSource.evenSquared p : K[X]).comp (4 * X) -
      WPFiniteLVSource.evenSquared p = WPFiniteWSource.deltaE p := by
  rw [WPFiniteLVSource.evenSquared, sum_comp, ← Finset.sum_sub_distrib, WPFiniteWSource.deltaE]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_comp, C_comp, pow_comp, X_comp, mul_pow]
  simp only [div_eq_mul_inv, map_mul, map_sub, map_pow, map_ofNat, map_one, one_mul]
  ring

theorem comparisonCoordinateI_field (hp : 19 ≤ p) :
    (comparisonCoordinateI p).map (WPPIntegralReduction.residueHom p) =
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]) := by
  simp only [comparisonCoordinateI, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    WPActualRankTwoHatLift.smallIntegralInverse_field p 5 (by omega) (by omega),
    WPFiniteWSource.squaredCoordinate, Nat.cast_ofNat]

theorem movingEvenIntegral_field (hp : 19 ≤ p) :
    (movingEvenIntegral p).map (WPPIntegralReduction.residueHom p) =
      (movingEvenField p : (ZMod p)[X]) := by
  simp only [movingEvenIntegral, Polynomial.map_sub, Polynomial.map_comp,
    Polynomial.map_mul, Polynomial.map_ofNat,
    ActualJointGreen.finiteEvenSquaredIntegral_field p hp, comparisonCoordinateI_field p hp]
  have he := congrArg (fun P : (ZMod p)[X] => P.comp WPFiniteWSource.squaredCoordinate)
    (evenSquared_scaled_difference (K := ZMod p) p)
  simpa only [sub_comp, comp_assoc, mul_comp, ofNat_comp, X_comp,
    Nat.cast_ofNat, movingEvenField] using he

/-- Whole Sbar reduction keeps the rational branch term until its own field zero. -/
theorem comparisonIntegral_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) (comparisonIntegral p) =
      (comparisonField p : (ZMod p)[T;T⁻¹]) := by
  have h4 : (4 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h4p : (4 : ZMod p) ^ p = 4 := ZMod.pow_card 4
  have hqp : (1 / 4 : ZMod p) ^ p = 1 / 4 := by rw [div_pow, one_pow, h4p]
  have hz : (17 : ZMod p) - 4 * ((1 / 4 : ZMod p) ^ p + (4 : ZMod p) ^ p) = 0 := by
    rw [h4p, hqp]
    field_simp [h4]
    ring
  have hi15 : WPPIntegralReduction.residueHom p
      (WPActualRankTwoHatLift.smallIntegralInverse p 15) = (1 / 15 : ZMod p) := by
    simpa only [Nat.cast_ofNat, one_div] using
      WPActualRankTwoHatLift.smallIntegralInverse_field p 15 (by omega) (by omega)
  have hi4 : WPPIntegralReduction.residueHom p
      (WPActualRankTwoHatLift.smallIntegralInverse p 4) = (1 / 4 : ZMod p) := by
    simpa only [Nat.cast_ofNat, one_div] using
      WPActualRankTwoHatLift.smallIntegralInverse_field p 4 (by omega) (by omega)
  have hbranchScalar : WPPIntegralReduction.residueHom p
      (WPActualRankTwoHatLift.smallIntegralInverse p 15 *
        (17 - 4 * ((WPActualRankTwoHatLift.smallIntegralInverse p 4) ^ p + 4 ^ p)) *
          comparisonEndIntegral p) = 0 := by
    simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, hi4]
    rw [hz, mul_zero, zero_mul]
  have hbranch : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 15 *
        (17 - 4 * ((WPActualRankTwoHatLift.smallIntegralInverse p 4) ^ p + 4 ^ p)) *
          comparisonEndIntegral p)) = 0 := by
    rw [WPActualChiSource.coefficientMap_C, hbranchScalar, map_zero]
  have hphase : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (comparisonPhaseIntegral p) = (WPFiniteZSource.phase p : (ZMod p)[T;T⁻¹]) := by
    simp only [comparisonPhaseIntegral, map_sub, map_mul, map_ofNat,
      WPActualChiSource.coefficientMap_T, WPFiniteZSource.phase]
  rw [comparisonIntegral, map_add, hbranch, add_zero,
    map_mul, map_mul, WPActualChiSource.coefficientMap_C, hi15, hphase,
    map_add, WPActualChiSource.coefficientMap_toLaurent,
    WPActualChiSource.coefficientMap_invert, WPActualChiSource.coefficientMap_toLaurent,
    movingEvenIntegral_field p hp]
  rfl

private theorem chiX_weighted_anti (p N e : ℕ) :
    WPActualEtaPole.chiX p N e + T (N : ℤ) *
      invert (WPActualEtaPole.chiX p N e) = (0 : ℚ[T;T⁻¹]) := by
  have hi (L : ℚ[T;T⁻¹]) : invert (invert L)=L :=
    LaurentPolynomial.involutive_invert L
  have hT : (T (N : ℤ) * T (-(N : ℤ)) : ℚ[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  simp only [WPActualEtaPole.chiX, map_mul, map_sub, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, ← WPActualChiSource.Fpull_reciprocal,
    hi]
  linear_combination -LaurentPolynomial.C (1 / (p : ℚ)) *
    WPActualPullbackSource.Fpull e WPActualEtaPole.Vx * hT

private theorem halfChiField_weighted_anti (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    WPFieldAssembly.NativeChiFieldSource.halfChiField p hp + T (((p-1)/2 : ℕ) : ℤ) *
      invert (WPFieldAssembly.NativeChiFieldSource.halfChiField p hp) = 0 := by
  let L := WPLaurentIntegralResidue.integralLift p
    (WPFieldAssembly.NativeShiftedChi.halfChiIntegral p hp)
  have hi : L + T (((p-1)/2 : ℕ) : ℤ) * invert L = 0 := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
    simp only [map_add, map_mul, map_zero, WPActualChiSource.coefficientMap_T,
      WPActualChiSource.coefficientMap_invert]
    rw [show WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype L =
      WPActualEtaPole.chiX p ((p-1)/2) ((p-1)/2) from
        WPLaurentIntegralResidue.integralLift_rational p _]
    exact chiX_weighted_anti p ((p-1)/2) ((p-1)/2)
  have hf := congrArg (WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)) hi
  change WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) L +
    T (((p-1)/2 : ℕ) : ℤ) * invert
      (WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p) L) = 0
  simpa only [
    map_add, map_mul, map_zero, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert] using hf

section NativeReflectionSeed
variable {K : Type*} [Field K]

theorem actual_chi_weighted_anti (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ActualThreePhase.χK (K := K) p hp + T (((p-1)/2 : ℕ) : ℤ) *
      invert (ActualThreePhase.χK (K := K) p hp) = 0 := by
  have he := congrArg (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p))
    (halfChiField_weighted_anti p hp)
  simpa only [ActualThreePhase.χK, map_add, map_mul, map_zero,
    WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert] using he

theorem actual_f_weighted_reflection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (ActualThreePhase.fK (K := K) p hp).toLaurent = T (((p-1)/2 : ℕ) : ℤ) *
      invert (ActualThreePhase.fK (K := K) p hp).toLaurent := by
  have hrec : (WPFieldAssembly.NativeChiFieldSource.halfPullbackField p hp).toLaurent =
      T (((p-1)/2 : ℕ) : ℤ) *
        invert (WPFieldAssembly.NativeChiFieldSource.halfPullbackField p hp).toLaurent := by
    rw [WPFieldAssembly.NativeChiFieldSource.halfPullbackField_eq,
      WPActualNativeHasse.actual_full_native_field_cutoff p ((p-1)/2)
        (by omega) (by omega) (by omega)]
    exact WPActualHasseReciprocal.actual_native_Hasse_Laurent p (by omega)
  have he := congrArg (WPActualChiSource.coefficientMap (ActualThreePhase.φ (K := K) p)) hrec
  simpa only [ActualThreePhase.fK, map_mul, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert, WPActualChiSource.coefficientMap_toLaurent] using he

private theorem zeta_phase_K (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (ActualChiEndpoints.zeta p : K[T;T⁻¹]) =
      LaurentPolynomial.C (1/3 : K) * WPFiniteZSource.phase p := by
  have hT : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  rw [ActualChiEndpoints.zeta, WPFiniteZSource.phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1/3 : K) * WPFiniteZSource.phase p * hT

private theorem zeta_invert_K (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    invert (ActualChiEndpoints.zeta p : K[T;T⁻¹]) = ActualChiEndpoints.zeta p := by
  rw [zeta_phase_K p hp]
  simp only [WPFiniteZSource.phase, map_mul, map_sub, map_ofNat,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T, neg_neg]
  ring

/-- Actual SB98 reflection seed, with the whole symmetric comparison and both proper halves. -/
theorem actual_reflection_seed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=1/5) :
    ActualChiEndpoints.zeta p *
        ((ActualThreePhase.CBK (K := K) p).toLaurent + T (((p-1)/2 : ℕ) : ℤ) *
          invert (ActualThreePhase.CBK (K := K) p).toLaurent) +
      (ActualThreePhase.fK (K := K) p hp).toLaurent * comparisonField p = 0 := by
  have ha := actual_chi_weighted_anti (K := K) p hp
  have hf := actual_f_weighted_reflection (K := K) p hp
  have hs := actual_P_symmetric_comparison (K := K) p hp u hu
  have hc := congrArg (fun L : K[T;T⁻¹] => L + T (((p-1)/2 : ℕ) : ℤ) * invert L)
    (WPFieldAssembly.ActualGreenResidue.actual_chi_finite_P (K := K) p hp u hu)
  simp only [map_add, map_mul, zeta_invert_K p hp] at hc
  linear_combination ha - hc -
    (ActualThreePhase.fK (K := K) p hp).toLaurent * hs +
    invert (WPFiniteZSource.P p u) * hf

end NativeReflectionSeed

section ReflectedDifference
variable {R : Type*} [CommRing R]
noncomputable def weightedReflectionDifference (N : ℕ) (L : R[T;T⁻¹]) : R[T;T⁻¹] :=
  L - T (N : ℤ) * invert L

theorem weightedReflectionDifference_anti (N : ℕ) (L : R[T;T⁻¹]) :
    weightedReflectionDifference N L + T (N : ℤ) *
      invert (weightedReflectionDifference N L) = 0 := by
  have hi (M : R[T;T⁻¹]) : invert (invert M)=M :=
    LaurentPolynomial.involutive_invert M
  have hT : (T (N : ℤ) * T (-(N : ℤ)) : R[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  simp only [weightedReflectionDifference, map_sub, map_mul,
    LaurentPolynomial.invert_T, hi]
  linear_combination -L * hT

end ReflectedDifference

noncomputable def midpointSigmaIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[X] :=
  NativeQuadraticInverse.quadraticInverse
    (WPActualRankTwoLegendreField.rankIntegralJacobi p (by omega) 1 *
      WPActualRankTwoResidueSource.rankDividedIntegralJacobi p (by omega))

noncomputable def midpointRemainderIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[X] :=
  NativeQuadraticInverse.quadraticInverse
    (NativeStrictTail.nativeSecondCorrectionHalfIntegral p hp)

noncomputable def midpointFIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[X] :=
  WPHasseIntegralTransport.nativeIntegral p ((p-1)/2) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- The actual half-native source and the actual p/3 low family agree through the prescribed first jet. -/
theorem actual_midpoint_precision_two (hp : 19 ≤ p) :
    midpointFIntegral p hp = NativeOriginalResidues.squareQIntegral p hp +
      Polynomial.C ((p : WPPIntegralReduction.integralRationals p) *
        WPActualRankTwoHatLift.smallIntegralInverse p 3) * midpointSigmaIntegral p hp +
      Polynomial.C ((p : WPPIntegralReduction.integralRationals p)^2) *
        midpointRemainderIntegral p hp := by
  apply Polynomial.map_injective (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
  have hthirdValue : (WPPIntegralReduction.integralRationals p).subtype
      ((p : WPPIntegralReduction.integralRationals p) *
        WPActualRankTwoHatLift.smallIntegralInverse p 3) = (p : ℚ) / 3 := by
    change (p : ℚ) * (WPActualRankTwoHatLift.smallIntegralInverse p 3).val = _
    rw [WPActualRankTwoHatLift.smallIntegralInverse_value p 3 (by omega) (by omega)]
    ring
  have hsecondValue : (WPPIntegralReduction.integralRationals p).subtype
      ((p : WPPIntegralReduction.integralRationals p)^2) = (p : ℚ)^2 := rfl
  simp only [midpointFIntegral, midpointSigmaIntegral, midpointRemainderIntegral,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    hthirdValue, hsecondValue, WPHasseIntegralTransport.nativeIntegral_map_rational,
    NativeOriginalResidues.squareQIntegral_value p hp,
    NativeQuadraticInverse.quadraticInverse_map,
    WPActualRankTwoLegendreField.rankIntegralJacobi_value,
    WPActualRankTwoResidueSource.rankDividedIntegralJacobi_value]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have hu : Polynomial.C ((p : ℚ)^2) * Polynomial.C (1 / (p : ℚ)^2) = (1 : ℚ[X]) := by
    rw [← Polynomial.C_mul]
    field_simp [hpq]
    simp only [Polynomial.C_1]
  have hthird : (2 : ℚ[X]) * Polynomial.C (p : ℚ) * Polynomial.C (1 / 6 : ℚ) =
      Polynomial.C ((p : ℚ) / 3) := by
    rw [show (2 : ℚ[X]) = Polynomial.C (2 : ℚ) from
        (_root_.map_natCast (Polynomial.C : ℚ →+* ℚ[X]) 2).symm,
      ← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 1
    ring
  have hraw : Polynomial.C ((p : ℚ)^2) *
      (NativeStrictTail.nativeSecondCorrectionHalfIntegral p hp).map
        (WPPIntegralReduction.integralRationals p).subtype =
      NativeDiscriminant.halfNativeJacobi p - WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2 -
        Polynomial.C ((p : ℚ)/3) *
          (WPActualRankTwoParameter.rankJacobiNode p 1 *
            WPActualRankTwoDividedDifference.rankDividedJacobi p) := by
    rw [NativeStrictTail.nativeSecondCorrectionHalfIntegral_value p hp,
      NativeStrictTail.nativeTwoNodeU_eq p hp, ← mul_assoc, hu, one_mul]
    linear_combination
      -(WPActualRankTwoParameter.rankJacobiNode p 1 *
        WPActualRankTwoDividedDifference.rankDividedJacobi p) * hthird
  have he := congrArg (NativeQuadraticInverse.quadraticInverse (R := ℚ)) hraw
  simp only [ActualNC77Chart.quadraticInverse_C_mul,
    NativeOriginalResidues.quadraticInverse_sub_local] at he
  rw [NativeDiscriminant.halfNativeJacobi,
    NativeQuadraticInverse.quadraticInverse_quadratic] at he
  unfold NativeOriginalResidues.squareQ
  linear_combination -he

noncomputable def midpointSigmaReflectionIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  weightedReflectionDifference ((p-1)/2)
    ((midpointSigmaIntegral p hp).comp (WPHasseIntegralTransport.integralV p (by omega))).toLaurent

noncomputable def midpointRemainderReflectionIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  weightedReflectionDifference ((p-1)/2)
    ((midpointRemainderIntegral p hp).comp (WPHasseIntegralTransport.integralV p (by omega))).toLaurent

noncomputable def actualReflectionDefectIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  WPLaurentIntegralResidue.integralLift p (NativeShiftedChi.halfChiIntegral p hp) -
    LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 3) *
      midpointSigmaReflectionIntegral p hp -
    LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
      midpointRemainderReflectionIntegral p hp

noncomputable def actualLowReflectionNumeratorIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  weightedReflectionDifference ((p-1)/2)
    ((NativeOriginalResidues.squareQIntegral p hp).comp
      (WPHasseIntegralTransport.integralV p (by omega))).toLaurent

private theorem midpointChiIntegral_source (hp : 19 ≤ p) :
    LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
      WPLaurentIntegralResidue.integralLift p (NativeShiftedChi.halfChiIntegral p hp) =
        weightedReflectionDifference ((p-1)/2)
          ((midpointFIntegral p hp).comp
            (WPHasseIntegralTransport.integralV p (by omega))).toLaurent := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
  simp only [map_mul,
    WPLaurentIntegralResidue.integralLift_rational, WPActualChiSource.coefficientMap_toLaurent,
    midpointFIntegral, WPHasseIntegralTransport.nativeIntegral_map_rational,
    Polynomial.map_comp, WPHasseIntegralTransport.integralV_map_rational,
    weightedReflectionDifference, map_sub, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert, map_natCast]
  change LaurentPolynomial.C (p : ℚ) * WPActualEtaPole.chiX p ((p-1)/2) ((p-1)/2) =
    ((WPReview.nativePolynomial (((p-1)/2)+1)).comp WPActualPullbackSource.Vpolynomial).toLaurent -
      T (((p-1)/2 : ℕ) : ℤ) * invert
        ((WPReview.nativePolynomial (((p-1)/2)+1)).comp WPActualPullbackSource.Vpolynomial).toLaurent
  rw [← WPActualChiSource.Fpull_toLaurent, WPActualEtaPole.chiX,
    ← WPActualChiSource.Fpull_reciprocal]
  have hu : LaurentPolynomial.C (p : ℚ) * LaurentPolynomial.C (1/(p : ℚ)) =
      (1 : ℚ[T;T⁻¹]) := by
    rw [← map_mul]
    field_simp [show (p : ℚ) ≠ 0 by positivity]
    simp only [map_one]
  linear_combination
    (WPActualPullbackSource.Fpull ((p-1)/2) WPActualEtaPole.Vx -
      T (((p-1)/2 : ℕ) : ℤ) * invert
        (WPActualPullbackSource.Fpull ((p-1)/2) WPActualEtaPole.Vx)) * hu

/-- Literal p times the actual reflection defect, before either coefficient reduction. -/
theorem actual_low_reflection_defect_source (hp : 19 ≤ p) :
    actualLowReflectionNumeratorIntegral p hp =
      LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
        actualReflectionDefectIntegral p hp := by
  have ht := congrArg
    (fun P : (WPPIntegralReduction.integralRationals p)[X] =>
      weightedReflectionDifference ((p-1)/2)
        (P.comp (WPHasseIntegralTransport.integralV p (by omega))).toLaurent)
    (actual_midpoint_precision_two p hp)
  simp only [weightedReflectionDifference, add_comp, mul_comp, C_comp,
    map_add, map_mul, Polynomial.toLaurent_C, LaurentPolynomial.invert_C] at ht
  have hc := midpointChiIntegral_source p hp
  unfold actualLowReflectionNumeratorIntegral actualReflectionDefectIntegral
    midpointSigmaReflectionIntegral midpointRemainderReflectionIntegral
    weightedReflectionDifference at *
  simp only [map_pow] at *
  linear_combination -hc - ht

/-- The residue is chi minus the whole native Sigma reflection. -/
theorem actual_reflection_defect_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (actualReflectionDefectIntegral p hp) =
        NativeChiFieldSource.halfChiField p hp -
          LaurentPolynomial.C (1/3 : ZMod p) *
            weightedReflectionDifference ((p-1)/2)
              ((ActualNormCrossAttachment.actualSigmaNative p hp).comp
                (WPHasseIntegralTransport.fieldV p)).toLaurent := by
  have hs : (midpointSigmaIntegral p hp).map (WPPIntegralReduction.residueHom p) =
      ActualNormCrossAttachment.actualSigmaNative p hp := by
    simp only [midpointSigmaIntegral, NativeQuadraticInverse.quadraticInverse_map,
      Polynomial.map_mul, WPActualRankTwoLegendreField.rankIntegralJacobi_field,
      ActualNormCrossAttachment.actualSigmaNative,
      WPActualRankTwoResidueSource.actualRankDividedField]
  have hchi : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (WPLaurentIntegralResidue.integralLift p (NativeShiftedChi.halfChiIntegral p hp)) =
      NativeChiFieldSource.halfChiField p hp := rfl
  have hi3 : WPPIntegralReduction.residueHom p
      (WPActualRankTwoHatLift.smallIntegralInverse p 3) = (1 / 3 : ZMod p) := by
    simpa only [Nat.cast_ofNat, one_div] using
      WPActualRankTwoHatLift.smallIntegralInverse_field p 3 (by omega) (by omega)
  have hpC : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p)) = 0 := by
    rw [WPActualChiSource.coefficientMap_C, map_natCast, ZMod.natCast_self, map_zero]
  have hsigma : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (midpointSigmaReflectionIntegral p hp) =
        weightedReflectionDifference ((p-1)/2)
          ((ActualNormCrossAttachment.actualSigmaNative p hp).comp
            (WPHasseIntegralTransport.fieldV p)).toLaurent := by
    simp only [midpointSigmaReflectionIntegral, weightedReflectionDifference,
      map_sub, map_mul, WPActualChiSource.coefficientMap_T,
      WPActualChiSource.coefficientMap_invert, WPActualChiSource.coefficientMap_toLaurent,
      Polynomial.map_comp, hs, WPHasseIntegralTransport.integralV_map_field]
  rw [actualReflectionDefectIntegral, map_sub, map_sub, map_mul,
    WPActualChiSource.coefficientMap_C, hi3, hsigma, map_mul,
    hpC, zero_mul, sub_zero, hchi]

noncomputable def actualCBIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[X] :=
  (contract 2 (Polynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 5) *
    X ^ p * (ActualGreenPrimitive.greenBIntegral p hp).comp
      (ActualGreenPrimitive.cubicTIntegral p))).comp (comparisonCoordinateI p)

noncomputable def actualAbarIntegral : (WPPIntegralReduction.integralRationals p)[X] :=
  (4-X)*(4*X-1)

noncomputable def actualZetaIntegral :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 3 *
    WPActualRankTwoHatLift.smallIntegralInverse p 5 ^ (2 * (p-1))) *
    T (-(p : ℤ)) * (actualAbarIntegral p).toLaurent ^ p

noncomputable def actualLowFIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  ((NativeOriginalResidues.squareQIntegral p hp).comp
    (WPHasseIntegralTransport.integralV p (by omega))).toLaurent

noncomputable def actualLowMIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ) * invert (actualLowFIntegral p hp)

noncomputable def actualBalancedNumeratorIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  actualZetaIntegral p * ((actualCBIntegral p hp).toLaurent +
    T (((p-1)/2 : ℕ) : ℤ) * invert (actualCBIntegral p hp).toLaurent) +
    actualLowMIntegral p hp * comparisonIntegral p

set_option maxHeartbeats 1000000 in
theorem actualCBIntegral_field (hp : 19 ≤ p) :
    (actualCBIntegral p hp).map (WPPIntegralReduction.residueHom p) =
      ActualFirstGreen.CB p := by
  have hB : (ActualGreenPrimitive.greenBIntegral p hp).map
      (WPPIntegralReduction.residueHom p) = ActualFirstGreen.B p := by
    rw [ActualGreenPrimitive.greenBIntegral, Polynomial.map_mul,
      ActualBalancedNodeAttachment.balancedFirstIntegral_field p hp,
      ActualGreenPrimitive.balancedProper_field p hp]
    rfl
  have hCBt : (Polynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 5) *
      X ^ p * (ActualGreenPrimitive.greenBIntegral p hp).comp
        (ActualGreenPrimitive.cubicTIntegral p)).map (WPPIntegralReduction.residueHom p) =
        ActualFirstGreen.CBt p := by
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_comp,
      hB, ActualGreenPrimitive.cubicTIntegral_field,
      WPActualRankTwoHatLift.smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [ActualFirstGreen.CBt, Nat.cast_ofNat, one_div]
  rw [actualCBIntegral, Polynomial.map_comp,
    map_contract (by norm_num : (2 : ℕ) ≠ 0), hCBt,
    comparisonCoordinateI_field p hp]
  rfl

theorem actualZetaIntegral_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (actualZetaIntegral p) = (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹]) := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have he : (1/5 : ZMod p) ^ (2*(p-1)) = 1 := by
    rw [Nat.mul_comm 2 (p-1), pow_mul,
      ZMod.pow_card_sub_one_eq_one (one_div_ne_zero h5), one_pow]
  have hscalar : WPPIntegralReduction.residueHom p
      (WPActualRankTwoHatLift.smallIntegralInverse p 3 *
        WPActualRankTwoHatLift.smallIntegralInverse p 5 ^ (2 * (p-1))) =
        (1/3 : ZMod p) := by
    rw [map_mul, map_pow,
      WPActualRankTwoHatLift.smallIntegralInverse_field p 3 (by omega) (by omega),
      WPActualRankTwoHatLift.smallIntegralInverse_field p 5 (by omega) (by omega)]
    simp only [Nat.cast_ofNat, ← one_div]
    rw [he, mul_one]
  have hA : (actualAbarIntegral p).map (WPPIntegralReduction.residueHom p) =
      (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    simp only [actualAbarIntegral, WPFiniteZSource.Abar, Polynomial.map_mul,
      Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  rw [actualZetaIntegral, map_mul, map_mul, WPActualChiSource.coefficientMap_C,
    hscalar, WPActualChiSource.coefficientMap_T, map_pow,
    WPActualChiSource.coefficientMap_toLaurent, hA]
  rfl

theorem actualLowFIntegral_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (actualLowFIntegral p hp) =
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent := by
  have hm := congrArg (fun P : (WPPIntegralReduction.integralRationals p)[X] =>
    P.map (WPPIntegralReduction.residueHom p)) (actual_midpoint_precision_two p hp)
  have hfirstZero : WPPIntegralReduction.residueHom p
      ((p : WPPIntegralReduction.integralRationals p) *
        WPActualRankTwoHatLift.smallIntegralInverse p 3) = 0 := by
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
  have hsecondZero : WPPIntegralReduction.residueHom p
      ((p : WPPIntegralReduction.integralRationals p)^2) = 0 := by
    rw [map_pow, map_natCast, ZMod.natCast_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    hfirstZero, hsecondZero, Polynomial.C_0, zero_mul,
    add_zero] at hm
  simp only [actualLowFIntegral, WPActualChiSource.coefficientMap_toLaurent,
    Polynomial.map_comp, WPHasseIntegralTransport.integralV_map_field]
  rw [← hm, midpointFIntegral, WPHasseIntegralTransport.nativeIntegral_map_field,
    NativeChiFieldSource.halfPullbackField_eq]

section ComparisonMap
variable {K L : Type*} [Field K] [Field L]

theorem comparisonField_map (p : ℕ) (f : K →+* L) :
    WPActualChiSource.coefficientMap f (comparisonField (K := K) p) =
      comparisonField (K := L) p := by
  simp only [comparisonField, movingEvenField, WPFiniteZSource.phase,
    WPFiniteWSource.deltaE, WPFiniteWSource.squaredCoordinate,
    map_mul, map_add, map_sub, map_pow, map_ofNat,
    map_natCast, map_inv₀, map_div₀, map_one,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_toLaurent, WPActualChiSource.coefficientMap_invert,
    Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_one, Polynomial.map_pow]

theorem actual_zeta_map (p : ℕ) (f : K →+* L) :
    WPActualChiSource.coefficientMap f (ActualChiEndpoints.zeta p : K[T;T⁻¹]) =
      (ActualChiEndpoints.zeta p : L[T;T⁻¹]) := by
  simp only [ActualChiEndpoints.zeta, WPFiniteZSource.Abar,
    map_mul, map_pow, map_div₀, map_one, map_ofNat,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_toLaurent,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_ofNat,
    Polynomial.map_X, Polynomial.map_one]
end ComparisonMap

theorem actualBalancedNumeratorIntegral_field_zero (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (actualBalancedNumeratorIntegral p hp) = 0 := by
  let K := AlgebraicClosure (ZMod p)
  let φ : ZMod p →+* K := ActualThreePhase.φ p
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : K) (by norm_num : 0 < (2 : ℕ))
  have hres : WPActualChiSource.coefficientMap (WPPIntegralReduction.residueHom p)
      (actualBalancedNumeratorIntegral p hp) =
        (ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹]) *
          ((ActualFirstGreen.CB p).toLaurent + T (((p-1)/2 : ℕ) : ℤ) *
            invert (ActualFirstGreen.CB p).toLaurent) +
          T (((p-1)/2 : ℕ) : ℤ) *
            invert (NativeChiFieldSource.halfPullbackField p hp).toLaurent *
              comparisonField p := by
    simp only [actualBalancedNumeratorIntegral, actualLowMIntegral,
      map_add, map_mul, WPActualChiSource.coefficientMap_T,
      WPActualChiSource.coefficientMap_invert,
      WPActualChiSource.coefficientMap_toLaurent,
      actualZetaIntegral_field p hp, actualCBIntegral_field p hp,
      actualLowFIntegral_field p hp, comparisonIntegral_field p hp]
  apply WPLaurentIntegralResidue.coefficientMap_injective φ φ.injective
  rw [map_zero, hres]
  simp only [map_add, map_mul, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert,
    WPActualChiSource.coefficientMap_toLaurent, actual_zeta_map,
    comparisonField_map]
  change (ActualChiEndpoints.zeta p : K[T;T⁻¹]) *
    ((ActualThreePhase.CBK (K := K) p).toLaurent + T (((p-1)/2 : ℕ) : ℤ) *
      invert (ActualThreePhase.CBK (K := K) p).toLaurent) +
    T (((p-1)/2 : ℕ) : ℤ) * invert (ActualThreePhase.fK (K := K) p hp).toLaurent *
      comparisonField p = 0
  rw [← actual_f_weighted_reflection (K := K) p hp]
  exact actual_reflection_seed (K := K) p hp u hu

noncomputable def actualBalancedNumeratorQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
    (actualBalancedNumeratorIntegral p hp)

noncomputable def actualBalancedDividedQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1/(p : ℚ)) * actualBalancedNumeratorQ p hp

theorem actualBalancedDividedQ_integral (hp : 19 ≤ p) :
    actualBalancedDividedQ p hp ∈ WPActualEtaIntegrality.integralLaurent p := by
  intro j
  have hF := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff j)
    (actualBalancedNumeratorIntegral_field_zero p hp)
  rw [WPActualChiSource.coefficientMap_coeff] at hF
  have hres : (((actualBalancedNumeratorIntegral p hp).coeff j).val : ZMod p) = 0 := hF
  have hi := WPActualChiSource.divide_prime_integral p
    ((actualBalancedNumeratorIntegral p hp).coeff j).val
    ((actualBalancedNumeratorIntegral p hp).coeff j).property hres
  have hc : (actualBalancedDividedQ p hp).coeff j =
      ((actualBalancedNumeratorIntegral p hp).coeff j).val / (p : ℚ) := by
    rw [actualBalancedDividedQ, ← LaurentPolynomial.smul_eq_C_mul]
    change (1/(p : ℚ)) * (actualBalancedNumeratorQ p hp).coeff j = _
    rw [actualBalancedNumeratorQ, WPActualChiSource.coefficientMap_coeff]
    change (1/(p : ℚ)) * ((actualBalancedNumeratorIntegral p hp).coeff j).val = _
    ring
  rw [hc]
  exact hi

noncomputable def actualBalancedDividedIntegral (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  WPLaurentIntegralResidue.integralLift p
    ⟨actualBalancedDividedQ p hp, actualBalancedDividedQ_integral p hp⟩

theorem actualBalancedDividedIntegral_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
      (actualBalancedDividedIntegral p hp) = actualBalancedDividedQ p hp :=
  WPLaurentIntegralResidue.integralLift_rational p _

theorem actual_balanced_whole_p_source (hp : 19 ≤ p) :
    LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
      actualBalancedDividedIntegral p hp = actualBalancedNumeratorIntegral p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (WPPIntegralReduction.integralRationals p).subtype Subtype.val_injective
  rw [map_mul, WPActualChiSource.coefficientMap_C, map_natCast,
    actualBalancedDividedIntegral_value, actualBalancedDividedQ]
  have hu : LaurentPolynomial.C (p : ℚ) * LaurentPolynomial.C (1/(p : ℚ)) =
      (1 : ℚ[T;T⁻¹]) := by
    rw [← map_mul]
    field_simp [show (p : ℚ) ≠ 0 by positivity]
    simp only [map_one]
  rw [← mul_assoc, hu, one_mul]
  rfl

private theorem actualAbarIntegral_invert :
    invert (actualAbarIntegral p).toLaurent =
      T (-2) * (actualAbarIntegral p).toLaurent := by
  have hA : (actualAbarIntegral p).toLaurent =
      17 * T 1 - 4 * T 2 - 4 := by
    simp only [actualAbarIntegral, map_mul, map_sub, map_ofNat,
      Polynomial.toLaurent_X, map_one]
    rw [show (T 2 : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) =
      T 1 * T 1 by rw [← T_add]; norm_num]
    ring
  have h20 : (T (-2) * T 2 : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) = 1 := by
    rw [← T_add]
    norm_num
  have h21 : (T (-2) * T 1 : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) = T (-1) := by
    rw [← T_add]
    norm_num
  rw [hA]
  simp only [map_sub, map_mul, map_ofNat, LaurentPolynomial.invert_T]
  linear_combination 4*h20 - 17*h21

private theorem actualZetaIntegral_invert :
    invert (actualZetaIntegral p) = actualZetaIntegral p := by
  have hT : (T (p : ℤ) * T (-2) ^ p :
      (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) = T (-(p : ℤ)) := by
    rw [T_pow, ← T_add]
    congr 1
    omega
  let a := (actualAbarIntegral p).toLaurent
  let b := LaurentPolynomial.C (WPActualRankTwoHatLift.smallIntegralInverse p 3 *
    WPActualRankTwoHatLift.smallIntegralInverse p 5 ^ (2*(p-1)))
  have ha : invert a = T (-2) * a := actualAbarIntegral_invert p
  have hb : invert b = b := LaurentPolynomial.invert_C _
  change invert (b * T (-(p : ℤ)) * a ^ p) = b * T (-(p : ℤ)) * a ^ p
  simp only [map_mul, map_pow, hb, LaurentPolynomial.invert_T, neg_neg, ha, mul_pow]
  calc
    b * T (p : ℤ) * (T (-2) ^ p * a ^ p) =
        b * (T (p : ℤ) * T (-2) ^ p) * a ^ p := by ring
    _ = b * T (-(p : ℤ)) * a ^ p := by rw [hT]

private theorem comparisonIntegral_invert :
    invert (comparisonIntegral p) = comparisonIntegral p := by
  have hi (L : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) :
      invert (invert L)=L := LaurentPolynomial.involutive_invert L
  simp only [comparisonIntegral, comparisonPhaseIntegral, map_add, map_mul,
    map_sub, map_ofNat, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, neg_neg, hi]
  ring

theorem actual_balanced_numerator_reflection (hp : 19 ≤ p) :
    T (((p-1)/2 : ℕ) : ℤ) * invert (actualBalancedNumeratorIntegral p hp) =
      actualBalancedNumeratorIntegral p hp +
        LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
          actualReflectionDefectIntegral p hp * comparisonIntegral p := by
  have hi (L : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) :
      invert (invert L)=L := LaurentPolynomial.involutive_invert L
  have hT : (T (((p-1)/2 : ℕ) : ℤ) * T (-(((p-1)/2 : ℕ) : ℤ)) :
      (WPPIntegralReduction.integralRationals p)[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hd := actual_low_reflection_defect_source p hp
  change actualLowFIntegral p hp - actualLowMIntegral p hp =
    LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) *
      actualReflectionDefectIntegral p hp at hd
  unfold actualLowMIntegral at hd
  simp only [actualBalancedNumeratorIntegral, actualLowMIntegral,
    map_add, map_mul, actualZetaIntegral_invert, comparisonIntegral_invert,
    LaurentPolynomial.invert_T, hi]
  linear_combination comparisonIntegral p * hd +
    (actualZetaIntegral p * (actualCBIntegral p hp).toLaurent +
      actualLowFIntegral p hp * comparisonIntegral p) * hT

theorem actual_balanced_quotient_reflection (hp : 19 ≤ p) :
    T (((p-1)/2 : ℕ) : ℤ) * invert (actualBalancedDividedIntegral p hp) =
      actualBalancedDividedIntegral p hp +
        actualReflectionDefectIntegral p hp * comparisonIntegral p := by
  have he := actual_balanced_numerator_reflection p hp
  rw [← actual_balanced_whole_p_source p hp] at he
  simp only [map_mul, LaurentPolynomial.invert_C] at he
  have hpC : LaurentPolynomial.C (p : WPPIntegralReduction.integralRationals p) ≠ 0 := by
    intro hz
    have hc := congrArg
      (fun L : (WPPIntegralReduction.integralRationals p)[T;T⁻¹] => L.coeff 0) hz
    have hzero : (0 : (WPPIntegralReduction.integralRationals p)[T;T⁻¹]).coeff 0 = 0 := rfl
    rw [LaurentPolynomial.C_apply, if_pos rfl, hzero] at hc
    have hp0 : (p : WPPIntegralReduction.integralRationals p) = 0 := hc
    have hq := congrArg Subtype.val hp0
    exact (show (p : ℚ) ≠ 0 by positivity) hq
  apply mul_left_cancel₀ hpC
  linear_combination he

end WPFieldAssembly.ActualBalancedTrace
