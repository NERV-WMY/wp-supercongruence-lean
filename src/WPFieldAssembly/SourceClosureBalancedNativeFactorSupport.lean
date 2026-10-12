import WPFieldAssembly.SourceClosureBalancedNativeFactorization
import WPFieldAssembly.SourceClosureBalancedNativeSupport
import WPFiniteZSupport

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeSupport
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.SourceClosureUVSupport
  WPFieldAssembly.SourceClosureUVFieldTransport

namespace WPFieldAssembly.SourceClosureBalancedNativeFactorSupport

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_proper_square_pullback_degree (hp : 19≤p) :
    (actualProperSquarePullback p).natDegree≤3*(p/6)-3 := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have hq : (5*X^2-1 : (ZMod p)[X]).natDegree=2 := by
    compute_degree
    exact h5
  have ht : (4*X^3-3*X : (ZMod p)[X]).natDegree=3 := by
    compute_degree
    · exact h4
    · norm_num
  have hn := WPActualRankTwoProper.properLegendreJacobi_degree p (by omega)
  have he := congrArg Polynomial.natDegree (actual_proper_square_pullback_conic p hp)
  rw [natDegree_comp,hq,natDegree_comp,ht,natDegree_pow] at he
  omega

theorem actual_proper_square_carrier_degree (hp : 19≤p) :
    (actualProperSquareCarrier p).natDegree≤p+3*(p/6)-3 := by
  have hs := WPFiniteZSupport.coordinate_degree (K:=ZMod p)
  have hsp : ((WPFiniteWSource.squaredCoordinate : (ZMod p)[X])^p).natDegree≤p := by
    rw [natDegree_pow]
    exact (Nat.mul_le_mul_left p hs).trans (by omega)
  have he := natDegree_mul_le_of_le hsp (actual_proper_square_pullback_degree p hp)
  dsimp only [actualProperSquareCarrier]
  exact he.trans (by omega)

/-- The full square plus high proper phase loses its apparent third positive band. -/
theorem actual_square_high_phase_bound (hp : 19≤p) :
    Above (3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
      (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p)
        (2*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3) := by
  rw [actual_proper_square_phase_cancellation p hp]
  have hz := (actual_zeta_bounds p hp).1
  have hc := Above_toLaurent _ _ (actual_proper_square_carrier_degree p hp)
  have hc' : Above (actualProperSquareCarrier p).toLaurent
      ((p : ℤ)+3*((p/6 : ℕ) : ℤ)-3) := by
    exact Above_mono hc (by omega)
  have hh : Above (6-4*T (-(p : ℤ)) : (ZMod p)[T;T⁻¹]) 0 := by
    simpa only [map_ofNat] using above_sub_same 0 _ _ (Above_C (6 : ZMod p))
      (Above_mono (Above_C_mul (above_T (-(p : ℤ))) (4 : ZMod p)) (by omega))
  simpa only [mul_comm (LaurentPolynomial.C (1/25 : ZMod p)) (ActualChiEndpoints.zeta p),
    show (p : ℤ)+((p : ℤ)+3*((p/6 : ℕ) : ℤ)-3)+0=
      2*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3 by ring] using
    Above_mul (Above_mul (Above_C_mul hz (1/25 : ZMod p)) hc') hh

theorem actual_reflected_square_local_bound (hp : 19≤p) :
    Above (T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))
      ((p : ℤ)+(((p-1)/2 : ℕ) : ℤ)) := by
  have hz := (actual_zeta_bounds p hp).2
  have he : Above (invert (actualProperSquareLocal p)) (p : ℤ) := by
    simpa only [actualProperSquareLocal,map_mul,invert_C,add_zero,
      mul_comm (LaurentPolynomial.C (1/5 : ZMod p)) (invert (ActualChiEndpoints.zeta p))] using
      Above_mul (Above_mul (Above_C_mul hz (1/5 : ZMod p))
        (Above_invert_toLaurent (actualProperSquareCarrier p)))
        (Above_invert_toLaurent (actualProperHighPhase p))
  simpa only [add_comm] using Above_shift he (((p-1)/2 : ℕ) : ℤ)

/-- Every proper-square contribution lies strictly below the actual positive detector. -/
theorem actual_proper_square_remainder_top_zero (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    (f*(3*ActualChiEndpoints.zeta p^2*LaurentPolynomial.C (1/25 : ZMod p)*
      (actualProperSquareCarrier p).toLaurent+actualProperSquareLocal p+
        T (((p-1)/2 : ℕ) : ℤ)*invert (actualProperSquareLocal p))).coeff
          (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=0 := by
  have hn := WPFiniteWSource.half_exponent p hp
  have hf := (actual_low_F_bounds p hp).1
  have hwhole := above_add_same (2*(p : ℤ)+3*((p/6 : ℕ) : ℤ)-3) _ _
    (actual_square_high_phase_bound p hp)
    (Above_mono (actual_reflected_square_local_bound p hp) (by omega))
  have he := Above_mul hf hwhole
  exact he _ (by omega)

/-- The actual Sigma reflection term also lies below the same positive detector. -/
theorem actual_sigma_reflection_remainder_top_zero (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let S := coefficientMap (residueHom p) (comparisonIntegral p)
    let B := T (((p-1)/2 : ℕ) : ℤ)*invert (actualSigmaPullback p hp).toLaurent
    (2*f*S*B).coeff (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=0 := by
  have hn := WPFiniteWSource.half_exponent p hp
  have hf := (actual_low_F_bounds p hp).1
  have hP := descendedP_bounds (K:=ZMod p) p hp
  have hS : Above (coefficientMap (residueHom p) (comparisonIntegral p))
      (3*(((p-1)/2 : ℕ) : ℤ)) := by
    rw [comparisonIntegral_field p hp,
      ←SourceClosureActualUVAttachment.descendedP_actual_comparison p hp]
    exact above_add_same _ _ _ hP.1 (Above_mono hP.2 (by omega))
  have hB : Above (T (((p-1)/2 : ℕ) : ℤ)*invert (actualSigmaPullback p hp).toLaurent)
      (((p-1)/2 : ℕ) : ℤ) := by
    simpa only [add_zero] using Above_shift (Above_invert_toLaurent (actualSigmaPullback p hp))
      (((p-1)/2 : ℕ) : ℤ)
  have he : Above (2*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*
      coefficientMap (residueHom p) (comparisonIntegral p)*
        (T (((p-1)/2 : ℕ) : ℤ)*invert (actualSigmaPullback p hp).toLaurent))
          (3*((p/6 : ℕ) : ℤ)+4*(((p-1)/2 : ℕ) : ℤ)) := by
    simpa only [map_ofNat,
      show (3*((p/6 : ℕ) : ℤ)+3*(((p-1)/2 : ℕ) : ℤ))+(((p-1)/2 : ℕ) : ℤ)=
        3*((p/6 : ℕ) : ℤ)+4*(((p-1)/2 : ℕ) : ℤ) by ring] using
      Above_mul (Above_mul (Above_C_mul hf (2 : ZMod p)) hS) hB
  exact he _ (by omega)

theorem actual_UV_square_product_top_zero (hp : 19≤p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    (6*f^2*actualNativeUVZeroBranch p hp).coeff
      (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ))=0 := by
  have hn := WPFiniteWSource.half_exponent p hp
  have hf := (actual_low_F_bounds p hp).1
  have h0 := (actual_UV_zero_branch_bounds p hp).1
  have he := Above_mul (Above_C_mul (Above_pow hf 2) (6 : ZMod p)) h0
  have hz := he (2*(p : ℤ)+6*((p/6 : ℕ) : ℤ)) (by norm_num only [Nat.cast_ofNat]; omega)
  simpa only [map_ofNat] using hz

end WPFieldAssembly.SourceClosureBalancedNativeFactorSupport
