import WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification
import WPFieldAssembly.SourceClosureBalancedNativeEndpoint

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedNativeFactorization
  WPFieldAssembly.SourceClosureBalancedNativeReciprocal
  WPFieldAssembly.SourceClosureBalancedNativeEndpoint
  WPFieldAssembly.SourceClosureBalancedNativeBetaIdentification

namespace WPFieldAssembly.SourceClosureBalancedNativeNormalization

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

noncomputable def actualBalancedBranchB : ZMod p :=
  -2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
    3*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
      (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)/2

/-- All three homogeneous coefficients are fixed by the SAME original carriers. -/
noncomputable def actualNativeHomogeneousR (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  let mu := actualMu p hp
  let b := actualBalancedBranchB p
  let beta := actualOriginalBeta p
  LaurentPolynomial.C ((48/25 : ZMod p)*(mu+b)-6*b-(13/2 : ZMod p)*(6*beta))+
    LaurentPolynomial.C ((24/25 : ZMod p)*(mu+b)-(9/4 : ZMod p)*(6*beta))*
      (T (p : ℤ)+T (-(p : ℤ)))+
    LaurentPolynomial.C (6*beta)*(T (2*(p : ℤ))+T (-2*(p : ℤ)))

theorem actual_branch_coefficient_value (hp : 19≤p) :
    12*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
      9*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)=
          -6*actualBalancedBranchB p := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  unfold actualBalancedBranchB
  field_simp [h2]
  ring

/-- No UV source, proper source, endpoint or extreme coefficient premise is supplied. -/
theorem actual_original_homogeneous_normalization (hp : 19≤p) :
    actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*
          actualNativeHomogeneousR p hp := by
  obtain ⟨R,hfactor,hR,_⟩ := actual_native_reciprocal_three_slots p hp
  have hbeta := actual_ratio_extreme_original_beta p hp R hfactor hR
  have hbranch := actual_native_reciprocal_branch_constraint p hp R hfactor hR
  rw [actual_branch_coefficient_value p hp] at hbranch
  have hend := actual_native_three_slot_unit_constraint p hp R hfactor hR
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have hn := three_slot_coefficient_normalization h2 h5
    (R.coeff 0) (R.coeff (p : ℤ)) (R.coeff (2*(p : ℤ)))
      (actualMu p hp) (actualBalancedBranchB p) hbranch hend
  have he : R=actualNativeHomogeneousR p hp := by
    rw [hR,hn.1,hn.2,hbeta]
    rfl
  rw [he] at hfactor
  exact hfactor

/-- The native particular is the specified actual printed numerator, with all
original homogeneous phases fixed by mu, the branch carry and original beta. -/
theorem actual_balanced_native_identification (hp : 19≤p) :
    actualBalancedField p hp=
      LaurentPolynomial.C (1/6 : ZMod p)*actualRootFreePrintedN p hp-
        LaurentPolynomial.C (1/6 : ZMod p)*
          (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
            actualNativeHomogeneousR p hp := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let E := actualBalancedField p hp
  let N := actualRootFreePrintedN p hp
  let R := actualNativeHomogeneousR p hp
  have hd := SourceClosureBalancedFirstSource.actual_balanced_multiplier_exact_degree p hp
  have hF : NativeChiFieldSource.halfPullbackField p hp≠0 := by
    intro hz
    rw [hz,natDegree_zero] at hd
    omega
  have hf : f≠0 := by
    intro hz
    apply hF
    apply Polynomial.toLaurent_injective
    simpa only [map_zero] using hz
  have h6 : (6 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 6
    (by omega) (by omega)
  have hunit : (6 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/6 : ZMod p)=1 := by
    change LaurentPolynomial.C (6 : ZMod p)*LaurentPolynomial.C (1/6 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h6,map_one]
  have hM := actual_original_homogeneous_normalization p hp
  change actualNativeClearedNumerator p hp-6*f*E=f^2*R at hM
  have hQ := actual_cleared_printed_factorization p hp
  change actualNativeClearedNumerator p hp=f*N at hQ
  change E=LaurentPolynomial.C (1/6 : ZMod p)*N-
    LaurentPolynomial.C (1/6 : ZMod p)*f*R
  apply mul_left_cancel₀ hf
  linear_combination -LaurentPolynomial.C (1/6 : ZMod p)*hM+
    LaurentPolynomial.C (1/6 : ZMod p)*hQ-f*E*hunit

end WPFieldAssembly.SourceClosureBalancedNativeNormalization
