import WPFieldAssembly.SourceClosureBalancedNativeFactorSupport
import WPFieldAssembly.SourceClosureBalancedNativeExtreme
import WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
import WPFieldAssembly.SourceClosureLaurentTopCoefficient
import WPFieldAssembly.SourceClosureVbalJCarrierNormalization

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureUVCanonicalHoles
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.SourceClosureBalancedNativeFactorSupport
  WPFieldAssembly.SourceClosureBalancedNativeExtreme
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureLaurentTopCoefficient
  WPFieldAssembly.SourceClosureVbalJCarrierNormalization

namespace WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The beta slot is the coefficient of the specified original whole Z. -/
noncomputable def actualOriginalBeta : ZMod p :=
  (originalDescendedZ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ))

theorem actual_original_beta_both_roots {K : Type*} [Field K] [CharP K p]
    (f : ZMod p →+* K) (hp : 19≤p) (u : K) (hu : u^2=1/5) :
    f (actualOriginalBeta p)=(WPFiniteZSource.Z p u).coeff (2*(p : ℤ)) := by
  have he := original_descended_Z_transport f p
  rw [original_descended_Z_original p hp u hu] at he
  have hc := congrArg (fun L : K[T;T⁻¹] => L.coeff (2*(p : ℤ))) he
  simpa only [coefficientMap_coeff,actualOriginalBeta] using hc

theorem actual_proper_J_pair_original (hp : 19≤p) :
    actualProperJLocal p+invert (actualProperJLocal p)=
      (3*WPFiniteJCarrier.GJ p : (ZMod p)[T;T⁻¹]) := by
  have hJ := actual_native_J_contraction (K:=ZMod p) p hp
  change actualNativeJCarrier p=Polynomial.C (1/5 : ZMod p)*WPFiniteJSource.HJP p at hJ
  simpa only [actualProperJLocal,hJ,ActualChiEndpoints.zeta] using
    actual_native_J_pair (K:=ZMod p) p hp

/-- The full actual particular is six f² times original Z plus explicit lower remainders. -/
theorem actual_cleared_original_Z_decomposition (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let S := coefficientMap (residueHom p) (comparisonIntegral p)
    let B := T (((p-1)/2 : ℕ) : ℤ)*
      invert (SourceClosureBalancedNativeParticular.actualSigmaPullback p hp).toLaurent
    actualNativeClearedNumerator p hp=
      6*f^2*originalDescendedZ p+6*f^2*actualNativeUVZeroBranch p hp+
        f*(3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
          (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
            T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))-2*f*S*B := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hhalf : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/2 : ZMod p)=1 := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/2 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  rw [actual_cleared_printed_factorization p hp]
  dsimp only [actualRootFreePrintedN,originalDescendedZ]
  rw [actual_proper_J_pair_original p hp]
  linear_combination
    3*(NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*descendedP p^2*hhalf

/-- The original beta coefficient, rather than a new free value, is extracted by Q6. -/
theorem actual_cleared_positive_original_beta (hp : 19≤p) :
    (actualNativeClearedNumerator p hp).coeff (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=
      6*(NativeChiFieldSource.halfPullbackField p hp).leadingCoeff^2*actualOriginalBeta p := by
  let j : ℤ := 2*(p : ℤ)+6*((p/6 : ℕ) : ℤ)
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  have hd := actual_low_F_square_strict_band p hp
  have hc := polynomial_times_laurent_top
    (NativeChiFieldSource.halfPullbackField p hp^2)
      (originalDescendedZ p : (ZMod p)[T;T⁻¹]) (2*(p : ℤ))
        (original_descended_Z_upper_bound p hp)
  rw [hd.1,leadingCoeff_pow,map_pow] at hc
  have hj : ((6*(p/6) : ℕ) : ℤ)+2*(p : ℤ)=j := by dsimp only [j]; push_cast; ring
  rw [hj] at hc
  have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff j)
    (actual_cleared_original_Z_decomposition p hp)
  simp only [AddMonoidAlgebra.coeff_sub,AddMonoidAlgebra.coeff_add,
    Finsupp.sub_apply,Finsupp.add_apply] at he
  rw [actual_UV_square_product_top_zero p hp,actual_proper_square_remainder_top_zero p hp,
    actual_sigma_reflection_remainder_top_zero p hp,add_zero,add_zero,sub_zero] at he
  have h6 : (6*f^2*originalDescendedZ p).coeff j=
      6*(f^2*originalDescendedZ p).coeff j := by
    simpa only [map_ofNat,mul_assoc] using
      constant_mul_coeff (6 : ZMod p) (f^2*originalDescendedZ p) j
  rw [h6,hc] at he
  change (actualNativeClearedNumerator p hp).coeff j=
    6*(NativeChiFieldSource.halfPullbackField p hp).leadingCoeff^2*
      (originalDescendedZ p : (ZMod p)[T;T⁻¹]).coeff (2*(p : ℤ))
  linear_combination he

theorem actual_ratio_extreme_original_beta (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R)
    (hR : R=LaurentPolynomial.C (R.coeff 0)+
      LaurentPolynomial.C (R.coeff (p : ℤ))*(T (p : ℤ)+T (-(p : ℤ)))+
      LaurentPolynomial.C (R.coeff (2*(p : ℤ)))*(T (2*(p : ℤ))+T (-2*(p : ℤ)))) :
    R.coeff (2*(p : ℤ))=6*actualOriginalBeta p := by
  apply mul_right_cancel₀ (actual_extreme_leading_coefficient_nonzero p hp)
  have hd := actual_cleared_positive_extreme p hp R hfactor hR
  have hb := actual_cleared_positive_original_beta p hp
  linear_combination hb-hd

end WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
