import WPFieldAssembly.SourceClosureBalancedNativeReflection
import WPFieldAssembly.SourceClosureBalancedNativeAlgebra

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualGreenPrimitive
  WPFieldAssembly.ActualBalancedNodeAttachment WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.SourceClosureActualUVAttachment WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.ActualCommonTraceReduction WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedUVSource WPFieldAssembly.SourceClosureBalancedNativeAlgebra

namespace WPFieldAssembly.SourceClosureBalancedNativeForcing

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_native_TB_field (hp : 19≤p) :
    coefficientMap (WPPIntegralReduction.residueHom p) (nativeTBIntegral p hp)=
      (actualTBPullback p).toLaurent := by
  have hB : (greenBIntegral p hp).map (WPPIntegralReduction.residueHom p)=
      ActualFirstGreen.B p := by
    rw [greenBIntegral,Polynomial.map_mul,balancedFirstIntegral_field p hp,
      balancedProper_field p hp]
    rfl
  rw [nativeTBIntegral,coefficientMap_toLaurent,Polynomial.map_comp,
    quadraticInverse_map,Polynomial.map_mul,Polynomial.map_X,hB,
    WPHasseIntegralTransport.integralV_map_field]
  rfl

/-- The original UV is normalized at the same branch used by the native particular. -/
noncomputable def actualNativeUVZeroBranch (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  actualUV p hp-LaurentPolynomial.C
    (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp))

theorem actual_native_UV_zero_branch_derivative (hp : 19≤p) :
    D (actualNativeUVZeroBranch p hp)=D (actualUV p hp) := by
  rw [actualNativeUVZeroBranch,map_sub,D_C,sub_zero]

/-- Q6 is formed from the actual carriers before any inverse of the low multiplier. -/
noncomputable def actualNativeClearedNumerator (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  clearedParticular (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    (coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperGIntegral p hp))
    (descendedP p)
    (coefficientMap (WPPIntegralReduction.residueHom p) (actualReflectionDefectIntegral p hp))
    (actualNativeUVZeroBranch p hp) (actualWholeProperParticular p hp)

/-- The actual native numerator and actual divided balanced carrier have identical full forcing.
No Sigma, UV, proper-source, endpoint or quadratic-root premise is supplied by a caller. -/
theorem actual_native_balanced_same_forcing (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let Q := actualNativeClearedNumerator p hp
    let E := actualBalancedField p hp
    nativeClearingL*(f*D Q-2*Q*D f)=6*f*nativeClearingL*(f*D E-E*D f) := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let G := coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperGIntegral p hp)
  let H := coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperHIntegral p hp)
  let U := coefficientMap (WPPIntegralReduction.residueHom p) (nativeProperUIntegral p)
  let delta := coefficientMap (WPPIntegralReduction.residueHom p) (actualReflectionDefectIntegral p hp)
  let S := coefficientMap (WPPIntegralReduction.residueHom p) (comparisonIntegral p)
  let sigma := coefficientMap (WPPIntegralReduction.residueHom p) (ActualSigmaIntegral.actualSigmaIntegral p hp)
  let TB := coefficientMap (WPPIntegralReduction.residueHom p) (nativeTBIntegral p hp)
  let P : (ZMod p)[T;T⁻¹] := descendedP p
  let T0 := actualNativeUVZeroBranch p hp
  let Tproper := actualWholeProperParticular p hp
  let E := actualBalancedField p hp
  let h := LaurentPolynomial.C (WPActualGaussBottom.fieldHarmonic p (p/6))
  let phase : (ZMod p)[T;T⁻¹] := T (-(((p-1)/2 : ℕ) : ℤ))
  have hmetric := actual_local_proper_metric_field p hp
  have hproper := actual_whole_proper_particular_source p hp
  dsimp only at hmetric hproper
  change nativeClearingL*(f*D G-G*D f)=U*f*(1-f) at hmetric
  rw [←actual_native_TB_field p hp] at hproper
  change nativeClearingL*(f*D Tproper-Tproper*D f)=
    U*(3*(f*P+G-delta)+h*f^2*(1-phase)+f*(TB-invert TB)) at hproper
  have hP := actual_P_native_cleared_source p hp
  change 2*nativeClearingL*D P=2*U-nativeClearingL*T (-1) at hP
  have hUV := actual_UV_native_cleared_source p hp
  have hSigma : commonSigmaField p hp=sigma := rfl
  rw [←actual_native_UV_zero_branch_derivative p hp,
    ←comparisonIntegral_field p hp,hSigma] at hUV
  change 2*nativeClearingL*D T0=
    2*nativeClearingL*sigma-2*nativeClearingGamma*S+
      nativeClearingL*T (-1)*(S-P) at hUV
  have hseed := actual_native_seed_field p hp
  change G+H+f*S=0 at hseed
  have hQ := cleared_particular_source f G H U nativeClearingL nativeClearingGamma
    delta S P T0 Tproper sigma TB (invert TB) phase h (T (-1))
    (D f) (D G) (D P) (D delta) (D T0) (D Tproper)
    hmetric hproper hP hUV hseed
  have hfirst := actual_native_first_source_cleared_field p hp
  dsimp only at hfirst
  change f*nativeClearingL*(f*D E-E*D f)=
    -nativeClearingGamma*f^3*S-
      LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*f^2*H*T (-1)+
      f*nativeClearingL*G*D delta-nativeClearingL*G*delta*D f-f^2*U*delta+
      LaurentPolynomial.C (1/3 : ZMod p)*h*f^3*U*(1-phase)+
      LaurentPolynomial.C (1/3 : ZMod p)*f^2*U*(TB-invert TB)+
      f^3*nativeClearingL*sigma at hfirst
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/2 : ZMod p)=1 := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/2 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  have hthird : (3 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/3 : ZMod p)=1 := by
    change LaurentPolynomial.C (3 : ZMod p)*LaurentPolynomial.C (1/3 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h3,map_one]
  change nativeClearingL*(f*D (clearedParticular f G P delta T0 Tproper)-
      2*clearedParticular f G P delta T0 Tproper*D f)=
    6*f*nativeClearingL*(f*D E-E*D f)
  rw [clearedParticular_derivative]
  linear_combination
    hQ-6*hfirst+3*nativeClearingL*f^2*H*T (-1)*hhalf-
      2*(h*f^3*U*(1-phase)+f^2*U*(TB-invert TB))*hthird

/-- The homogeneous ratio equation is obtained for the actual carriers, without dividing by f. -/
theorem actual_native_balanced_cleared_ratio (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    f*D (actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp)-
      2*(actualNativeClearedNumerator p hp-6*f*actualBalancedField p hp)*D f=0 := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  have hs := actual_native_balanced_same_forcing p hp
  dsimp only at hs
  exact same_forcing_cleared_ratio f nativeClearingL (actualBalancedField p hp)
    (actualNativeClearedNumerator p hp)
    (6*f*nativeClearingL*(f*D (actualBalancedField p hp)-actualBalancedField p hp*D f))
    (nativeClearingL_ne_zero p hp) rfl hs

end WPFieldAssembly.SourceClosureBalancedNativeForcing
