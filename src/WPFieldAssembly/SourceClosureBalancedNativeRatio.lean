import WPFieldAssembly.SourceClosureBalancedNativeForcing
import WPFieldAssembly.SourceClosureLaurentRatioDivision

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPActualRankTwoLegendreField WPActualRankTwoProper WPActualRankTwoComparison
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureLaurentRatioDivision

namespace WPFieldAssembly.SourceClosureBalancedNativeRatio

set_option maxHeartbeats 1600000

/-- The original proper Bezout identity remains polynomial after the cubic conic. -/
theorem cubic_proper_wronskian {K : Type*} [Field K] (h3 : (3 : K)≠0)
    (Y n : K[X])
    (hw : (1-X^2)*(Y*n.derivative-Y.derivative*n)=1-Y^2) :
    Polynomial.C (1/3 : K)*(1-X^2)*(4*X^2-1)*
      ((Y.comp (4*X^3-3*X))*(n.comp (4*X^3-3*X)).derivative-
        (Y.comp (4*X^3-3*X)).derivative*(n.comp (4*X^3-3*X)))=
      1-(Y.comp (4*X^3-3*X))^2 := by
  let T : K[X] := 4*X^3-3*X
  let q : K[X] := 1-X^2
  let b : K[X] := 4*X^2-1
  have hdt : T.derivative=3*b := by
    dsimp only [T,b]
    norm_num [derivative_sub,derivative_mul,derivative_pow,derivative_ofNat,C_ofNat]
    ring
  have hq : q.comp T=q*b^2 := by
    dsimp only [q,b,T]
    simp only [sub_comp,one_comp,pow_comp,X_comp]
    ring
  have hs := congrArg (fun P : K[X] => P.comp T) hw
  change (q*(Y*n.derivative-Y.derivative*n)).comp T=(1-Y^2).comp T at hs
  simp only [mul_comp,sub_comp,pow_comp,one_comp,hq] at hs
  have hi : (Polynomial.C (1/3 : K) : K[X])*3=1 := by
    change Polynomial.C (1/3 : K)*Polynomial.C (3 : K)=1
    rw [←Polynomial.C_mul,one_div_mul_cancel h3,Polynomial.C_1]
  change Polynomial.C (1/3 : K)*q*b*((Y.comp T)*(n.comp T).derivative-
    (Y.comp T).derivative*(n.comp T))=1-(Y.comp T)^2
  rw [derivative_comp,derivative_comp,hdt]
  linear_combination hs+q*b^2*((Y.comp T)*(n.derivative.comp T)-
    (Y.derivative.comp T)*(n.comp T))*hi

/-- The actual numerator difference is f squared times a whole derivative-invisible Laurent carrier.
Existence uses the actual proper Wronskian and the actual SB99 forcing, with no caller premise. -/
theorem actual_native_balanced_ratio_exists (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    ∃ R : (ZMod p)[T;T⁻¹],
      actualNativeClearedNumerator p hp-
        6*f*WPFieldAssembly.SourceClosureBalancedFirstSource.actualBalancedField p hp=
        f^2*R ∧ D R=0 := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let T : (ZMod p)[X] := 4*X^3-3*X
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hy : Y.comp T≠0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
    have ht : T.eval 1=1 := by dsimp only [T]; norm_num
    exact one_ne_zero (by
      simpa only [eval_comp,ht,Y,
        WPActualRankTwoComparison.actualLegendreJacobi_endpoint_one,eval_zero] using he)
  exact conic_laurent_ratio_division p (by omega)
    (NativeChiFieldSource.halfPullbackField p hp)
    (Polynomial.C (1/3 : ZMod p)*(1-X^2)*(4*X^2-1)) (Y.comp T) (n.comp T)
    (actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
        WPFieldAssembly.SourceClosureBalancedFirstSource.actualBalancedField p hp)
    hy h2 h3 h4 h5 (actual_low_F_conic_field p hp)
    (cubic_proper_wronskian h3 Y n (properLegendreJacobi_wronskian p (by omega)))
    (actual_native_balanced_cleared_ratio p hp)

end WPFieldAssembly.SourceClosureBalancedNativeRatio
