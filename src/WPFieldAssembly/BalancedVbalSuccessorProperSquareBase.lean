import WPFieldAssembly.ActualNormCrossAttachment
import WPFieldAssembly.NativeClosureReflectionSource

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
  WPFieldAssembly.ActualNormCrossAttachment WPFieldAssembly.NativeIR28
  WPFieldAssembly.ActualConicDescent

namespace WPFieldAssembly.SourceClosureBalancedNativeFactorization

set_option maxHeartbeats 1600000
variable (p : ℕ) [Fact p.Prime]

/- These are the unchanged actual proper-square definitions and full conic/
phase proofs. They depend only on checked native source inputs; the balanced
forcing and particular solution are not needed for this exact square source. -/

/-- The entire original proper square, with its integral quadratic inverse retained. -/
noncomputable def actualProperSquarePullback : (ZMod p)[X] :=
  (actualProperSquareNative p).comp (WPHasseIntegralTransport.fieldV p)

noncomputable def actualProperSquareCarrier : (ZMod p)[X] :=
  (WPFiniteWSource.squaredCoordinate : (ZMod p)[X])^p*actualProperSquarePullback p

/-- Tc=t(4t²-3); this factor is essential in the high proper phase. -/
noncomputable def actualProperHighPhase : (ZMod p)[X] :=
  (4*WPFiniteWSource.squaredCoordinate-3)^p


theorem actual_conic_polynomial_injective (hp : 19≤p) :
    Function.Injective (fun P : (ZMod p)[X] => P.comp (5*X^2-1)) := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hd : (5*X^2-1 : (ZMod p)[X]).natDegree=2 := by
    compute_degree
    exact h5
  exact WPFieldAssembly.ConicKernel.comp_injective_nonconstant _
    (by rw [hd]; norm_num)

theorem actual_proper_square_pullback_conic (hp : 19≤p) :
    (actualProperSquarePullback p).comp (5*X^2-1)=
      (WPActualRankTwoProper.properLegendreJacobi p^2).comp (4*X^3-3*X) := by
  have he := even_native_attachment p hp
    (WPActualRankTwoProper.properLegendreJacobi p^2) (actual_proper_square_even p hp)
  have hv : (WPHasseIntegralTransport.fieldV p).comp (5*X^2-1)=
      (1-(4*X^3-3*X)^2 : (ZMod p)[X]) := by
    simpa only [WPFiniteJHighCoefficient.conic,WPFiniteCubicLog.Tc] using
      WPActualNativeJacobiJet.actual_native_V_conic p hp
  rw [actualProperSquarePullback,actualProperSquareNative,comp_assoc,
    hv,
    show (1-(4*X^3-3*X)^2 : (ZMod p)[X])=
      (1-X^2 : (ZMod p)[X]).comp (4*X^3-3*X) by
        simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,he]


noncomputable def actualProperSquareLocal : (ZMod p)[T;T⁻¹] :=
  ActualChiEndpoints.zeta p*LaurentPolynomial.C (1/5 : ZMod p)*
    (actualProperSquareCarrier p).toLaurent*(actualProperHighPhase p).toLaurent


/-- The high proper phase retains its actual cubic factor after Frobenius. -/
theorem actual_proper_high_phase_frobenius (hp : 19≤p) :
    5*(actualProperHighPhase p).toLaurent=4*T (p : ℤ)-11 := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hunit : (5 : (ZMod p)[X])*Polynomial.C (1/5 : ZMod p)=1 := by
    change Polynomial.C (5 : ZMod p)*Polynomial.C (1/5 : ZMod p)=1
    rw [←Polynomial.C_mul,mul_one_div_cancel h5,Polynomial.C_1]
  have hb : (5*(4*WPFiniteWSource.squaredCoordinate-3) : (ZMod p)[X])=4*X-11 := by
    unfold WPFiniteWSource.squaredCoordinate
    simp only [one_div] at hunit
    linear_combination 4*(X+1)*hunit
  have hc (n : ℕ) : (n : (ZMod p)[X])^p=n := by
    have he := congrArg (Polynomial.C : ZMod p →+* (ZMod p)[X])
      (ZMod.pow_card (n : ZMod p))
    simpa only [map_pow,map_natCast] using he
  have h5p : (5 : (ZMod p)[X])^p=5 := by
    simpa only [Nat.cast_ofNat] using hc 5
  have h4p : (4 : (ZMod p)[X])^p=4 := by
    simpa only [Nat.cast_ofNat] using hc 4
  have h11p : (11 : (ZMod p)[X])^p=11 := by
    simpa only [Nat.cast_ofNat] using hc 11
  have he := congrArg (fun P : (ZMod p)[X] => P^p) hb
  rw [mul_pow,h5p] at he
  have hr : (4*X-11 : (ZMod p)[X])^p=4*X^p-11 := by
    rw [sub_pow_char,mul_pow,h4p,h11p]
  rw [hr] at he
  have he' := congrArg (fun P : (ZMod p)[X] => P.toLaurent) he
  simpa only [map_mul,map_sub,map_ofNat,Polynomial.toLaurent_X_pow,
    actualProperHighPhase] using he'

/-- The entire square and high phase cancel their apparent highest positive band. -/
theorem actual_proper_square_phase_cancellation (hp : 19≤p) :
    3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p=
      ActualChiEndpoints.zeta p*LaurentPolynomial.C (1/25 : ZMod p)*
        (actualProperSquareCarrier p).toLaurent*(6-4*T (-(p : ℤ))) := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have hthird : (3 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/3 : ZMod p)=1 := by
    change LaurentPolynomial.C (3 : ZMod p)*LaurentPolynomial.C (1/3 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h3,map_one]
  have hz : 3*(ActualChiEndpoints.zeta p : (ZMod p)[T;T⁻¹])=WPFiniteZSource.phase p := by
    rw [WPFieldAssembly.ActualBpairContraction.native_zeta_phase p hp,←mul_assoc,hthird,one_mul]
  have hscale : (1/5 : ZMod p)=5*(1/25) := by
    field_simp [h5,h25]
    ring
  have hCscale := congrArg (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) hscale
  simp only [map_mul,map_ofNat] at hCscale
  have hh := actual_proper_high_phase_frobenius p hp
  have hphase : 3*ActualChiEndpoints.zeta p+5*(actualProperHighPhase p).toLaurent=
      (6-4*T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) := by
    rw [hz,hh]
    unfold WPFiniteZSource.phase
    ring
  unfold actualProperSquareLocal
  rw [hCscale]
  linear_combination ActualChiEndpoints.zeta p*LaurentPolynomial.C (1/25 : ZMod p)*
    (actualProperSquareCarrier p).toLaurent*hphase


end WPFieldAssembly.SourceClosureBalancedNativeFactorization
