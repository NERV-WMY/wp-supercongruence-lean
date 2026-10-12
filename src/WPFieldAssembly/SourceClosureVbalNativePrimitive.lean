import WPActualRankTwoComparison
import WPFiniteKSource

open scoped Polynomial
open Polynomial WPActualRankTwoLegendreField WPActualRankTwoComparison
  WPActualRankTwoProper WPActualRankTwoResidueSource WPActualGaussBottom

namespace WPFieldAssembly.SourceClosureVbalNativePrimitive

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The actual divided rank-two source retains its whole logarithm and high proper phase. -/
theorem actual_rank_literal_source (hp : 19≤p) :
    actualRankDividedField p (by omega)=actualLegendreJacobi p*
      (WPFiniteKSource.LPsrc p-C (fieldHarmonic p (p/6)))-
        X^p*properLegendreJacobi p := by
  rw [actual_rankDividedField_eq_hat p hp]
  dsimp only [rankHatField,WPFiniteKSource.LPsrc,WPFiniteKSource.EP,
    WPFiniteNC122.q,evenLogPolynomial]
  simp only [map_sub]
  ring

/-- The finite native proper primitive keeps the entire T^p*n^2 and J_L cutoffs. -/
noncomputable def actualNativeProperPrimitive (hp : 19≤p) : (ZMod p)[X] :=
  properLegendreJacobi p*actualRankDividedField p (by omega)+
    C (1/2 : ZMod p)*X^p*properLegendreJacobi p^2+
      actualLegendreJacobi p^2*WPFiniteKSource.JLP p

/-- IR56's native primitive integrates Sigma and both SB99 extra forcing terms together. -/
theorem actual_native_proper_primitive_source (hp : 19≤p) :
    let Y := actualLegendreJacobi p
    let n := properLegendreJacobi p
    let F := Y^2
    let H := actualNativeProperPrimitive p hp
    (1-X^2)*(F*H.derivative-F.derivative*H)=
      Y*actualRankDividedField p (by omega)+C (fieldHarmonic p (p/6))*F^2+
        X*F*(Y*n) := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let A := WPFiniteKSource.LPsrc p-C (fieldHarmonic p (p/6))
  have hw : (1-X^2)*(Y*n.derivative-Y.derivative*n)=1-Y^2 :=
    properLegendreJacobi_wronskian p (by omega)
  have hA : (1-X^2)*A.derivative=X-X^p := by
    dsimp only [A]
    rw [derivative_sub,derivative_C,sub_zero]
    exact WPFiniteKSource.LPsrc_cleared_derivative p hp
  have hJ := WPFiniteKSource.JLP_cleared_derivative (K:=ZMod p) p hp
  have hLA : WPFiniteKSource.LPsrc p=A+C (fieldHarmonic p (p/6)) := by
    dsimp only [A]
    ring
  have hXp : (X^p : (ZMod p)[X]).derivative=0 := by
    rw [derivative_X_pow,ZMod.natCast_self,Polynomial.C_0,zero_mul]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[X])*C (1/2 : ZMod p)=1 := by
    change C (2 : ZMod p)*C (1/2 : ZMod p)=1
    rw [←C_mul,mul_one_div_cancel h2,C_1]
  dsimp only
  simp only [actualNativeProperPrimitive,actual_rank_literal_source p hp]
  change (1-X^2)*(Y^2*
      (n*(Y*A-X^p*n)+C (1/2 : ZMod p)*X^p*n^2+Y^2*WPFiniteKSource.JLP p).derivative-
      (Y^2).derivative*(n*(Y*A-X^p*n)+C (1/2 : ZMod p)*X^p*n^2+
        Y^2*WPFiniteKSource.JLP p))=
      Y*(Y*A-X^p*n)+C (fieldHarmonic p (p/6))*(Y^2)^2+X*Y^2*(Y*n)
  simp only [derivative_add,derivative_sub,derivative_mul,derivative_sq,
    derivative_C,hXp,zero_mul,mul_zero,zero_add,add_zero,C_ofNat]
  linear_combination (Y^2*A-X^p*Y*n)*hw+Y^3*n*hA+Y^4*hJ+
    (1-X^2)*X^p*Y*n*(Y*n.derivative-Y.derivative*n)*hhalf+Y^4*hLA

end WPFieldAssembly.SourceClosureVbalNativePrimitive
