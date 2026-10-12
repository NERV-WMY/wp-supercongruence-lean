import WPFieldAssembly.NativeScalarRows
import WPMomentPrecision.MomentToField

open scoped Polynomial
open Polynomial WPPIntegralReduction
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ActualNC77Chart
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.OriginalLaurentDensity
  WPFieldAssembly.ActualR0Node WPFieldAssembly.NativeScalarRows
  WPMomentPrecision.NativeQSource WPMomentPrecision.OriginalNegativeDigit
  WPMomentPrecision.RationalEulerPrimitive

namespace WPFieldAssembly.ActualNC77NativeAttachment

set_option maxHeartbeats 1000000

/-- The complete rational fold and the quadratic inverse select the same original norm. -/
theorem actualU2Q_eq_normQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    actualU2Q p=normQ p := by
  have h := congrArg quadraticInverse (actual_U2_q_source p hp)
  rw [quadraticInverse_quadratic] at h
  exact h

theorem actualYUQ_eq_mixedQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    actualYUQ p=mixedQ p := by
  have h := congrArg quadraticInverse (actual_YU_q_source p hp)
  rw [quadraticInverse_quadratic] at h
  exact h

theorem nativeTerm_eq_squareQ (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPActualNativeChiTaylor.nativeTermPolynomial p=squareQ p := by
  have h := congrArg quadraticInverse
    (WPActualTerminatingSquare.actual_terminating_Jacobi_square p hp)
  rw [quadraticInverse_quadratic] at h
  exact h

/-- The two Euler cutoffs agree on the complete supported polynomial, including zero. -/
theorem unitEuler_rationalEuler (p e : ℕ) (P : ℚ[X])
    (he : e<p) (hP : P.natDegree≤e) :
    unitEuler p P=rationalEuler e P := by
  ext n
  rw [unitEuler_coeff,rationalEuler_coeff]
  by_cases hn : n<e+1
  · rw [if_pos hn,if_pos (by omega : n<p)]
  · rw [if_neg hn]
    by_cases hnp : n<p
    · rw [if_pos hnp,coeff_eq_zero_of_natDegree_lt (hP.trans_lt (by omega)),zero_div]
    · rw [if_neg hnp]

/-- Both actual central digits use the same rational node and literal R0 before division. -/
theorem actualDeltaU_eq_native (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPMomentPrecision.OriginalCentralDigit.actualDeltaU p=ActualR0Node.actualDeltaU p := by
  unfold WPMomentPrecision.OriginalCentralDigit.actualDeltaU
    WPMomentPrecision.OriginalCentralDigit.actualCentralLeading
    ActualR0Node.actualDeltaU r0NodeBaseline
  rw [actualYUQ_eq_mixedQ p hp,nativeTerm_eq_squareQ p hp,
    ←unitEuler_rationalEuler p (p-1-p/6) (squareQ p) (by omega)
      ((actual_squareQ_degree p hp).trans (by omega))]
  rfl

theorem actual_deltaU_digit_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    ((WPMomentPrecision.OriginalCentralDigit.actualDeltaU p/(p : ℚ) : ℚ) : ZMod p)=
      residueHom p (integralDeltaUDigit p hp) := by
  rw [actualDeltaU_eq_native p hp]
  rfl

/-- Both original Laurent slots pass to the same whole integral norm polynomial. -/
theorem actual_originalI_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) (j : ℕ) :
    (originalI p j (actualU2Q p) : ZMod p)=
      ResidualProjection.Ij p j
        ((integralNormQ p (by omega)).map (residueHom p)) := by
  rw [actualU2Q_eq_normQ p hp]
  change (O p j (normQ p) : ZMod p)=_
  rw [←integralNormQ_value p (by omega)]
  exact original_projection_field p hp j _

theorem actual_Bpair_eq_native (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPMomentPrecision.ResonancePair.Bpair p hp=nativeBpair p hp := rfl

/-- The original rational Fermat quotient equals its integer lift before reduction. -/
theorem fermatQ_eq_integer (p a : ℕ) :
    WPMomentPrecision.BasePole.fermatQ p a=
      (WPFiniteInversion.integerFermatQuotient p (a : ℤ) : ℚ) := rfl

/-- P_p reduces from its actual integral arithmetic digit, including the full R(16) term. -/
theorem actualP_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (WPMomentPrecision.MomentPrecision.actualP p : ZMod p)=
      (304/3 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
      11*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)-
      11*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)-
      9*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)-
      3*(WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)^2-
      3*(WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)^2+
      (5/12 : ZMod p)*WPFiniteInversion.R p 16 := by
  let q : integralRationals p := WPFiniteInversion.integerFermatQuotient p 2
  let r : integralRationals p := WPFiniteInversion.integerFermatQuotient p 3
  let k : integralRationals p := WPFiniteInversion.integerFermatQuotient p 5
  let A : integralRationals p :=
    ⟨WPMomentPrecision.BasePole.actualAlpha p,WPMomentPrecision.BasePole.actualAlpha_integral p⟩
  let P : integralRationals p := 304*WPActualRankTwoHatLift.smallIntegralInverse p 3*q^2-
    11*q*r-11*q*k-9*r*k-3*r^2-3*k^2+
    5*WPActualRankTwoHatLift.smallIntegralInverse p 12*A
  have hv : P.val=WPMomentPrecision.MomentPrecision.actualP p := by
    unfold WPMomentPrecision.MomentPrecision.actualP WPMomentPrecision.MomentDigitAlgebra.arithmeticDigit
    rw [fermatQ_eq_integer p 2,fermatQ_eq_integer p 3,fermatQ_eq_integer p 5]
    change (integralRationals p).subtype P=_
    simp only [P,q,r,k,A,map_add,map_sub,map_mul,map_pow,map_ofNat,map_intCast,
      Subring.subtype_apply,WPActualRankTwoHatLift.smallIntegralInverse_value p 3 (by omega) (by omega),
      WPActualRankTwoHatLift.smallIntegralInverse_value p 12 (by omega) (by omega)]
    ring
  rw [←hv]
  change residueHom p P=_
  simp only [P,q,r,k,A,map_add,map_sub,map_mul,map_pow,map_ofNat,map_intCast,
    WPActualRankTwoHatLift.smallIntegralInverse_field p 3 (by omega) (by omega),
    WPActualRankTwoHatLift.smallIntegralInverse_field p 12 (by omega) (by omega)]
  change _+(5*(12 : ZMod p)⁻¹)*(WPMomentPrecision.BasePole.actualAlpha p : ZMod p)=_
  rw [WPMomentPrecision.BasePole.actualAlpha_residue]
  ring

/-- The actual Moment scalar is the native coupled row, with neither norm slot removed. -/
theorem actualNC77Scalar_native (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPMomentPrecision.MomentToField.actualNC77Scalar p hp=
      2*residueHom p (integralDeltaUDigit p hp)-
        (originalNorm p : ZMod p)-nativeBpair p hp := by
  rw [WPMomentPrecision.MomentToField.actualNC77Scalar,
    actual_deltaU_digit_field p hp,actual_Bpair_eq_native p hp,actual_originalI_field p hp 0,
    actual_originalI_field p hp 1,original_norm_field p hp]
  change 2*residueHom p (integralDeltaUDigit p hp)-
    12*ResidualProjection.Ij p 0 ((integralNormQ p (by omega)).map (residueHom p))-
    (15/2 : ZMod p)*ResidualProjection.Ij p 1
      ((integralNormQ p (by omega)).map (residueHom p))-nativeBpair p hp=_
  ring

end WPFieldAssembly.ActualNC77NativeAttachment
