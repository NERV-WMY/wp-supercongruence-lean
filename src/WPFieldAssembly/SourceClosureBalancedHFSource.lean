import WPFieldAssembly.SourceClosureBalancedOriginalDensity

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualKwFieldTrace WPFieldAssembly.ActualCommonTraceReduction
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureBalancedNativeBetaTransport
  WPFieldAssembly.SourceClosureBalancedOriginalDensity
  WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureCommonWholeSource

namespace WPFieldAssembly.SourceClosureBalancedHFSource

set_option maxHeartbeats 1800000

variable (p : ℕ) [Fact p.Prime]

/-- The exact polynomial clearing of the original cubic logarithmic differential. -/
theorem original_HF_polynomial_clearing {K : Type*} [Field K] :
    2*T 1*(T 1+1)*(delta : K[T;T⁻¹])+R*nativeClearingGamma=
      3*T 1^2*(WPFiniteZSource.Abar : K[X]).toLaurent*(4*T 1-1) := by
  have h2 : (T 2 : K[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
  have h3 : (T 3 : K[T;T⁻¹])=T 1^3 := by rw [T_pow]; norm_num
  rw [delta_expansion]
  simp only [R,nativeClearingGamma,WPFiniteZSource.Abar,map_mul,map_sub,
    map_ofNat,map_one,Polynomial.toLaurent_X,h2,h3]
  ring

/-- The actual positive branch and the full odd J derivative share one cleared source. -/
theorem actual_Bgamma_Z_cleared (hp : 19≤p) :
    (nativeClearingL : (ZMod p)[T;T⁻¹])*
        (descendedBgamma p hp+D (originalDescendedZ p))=
      -nativeClearingGamma*comparisonField p+
      LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*T (-1)*comparisonField p+
      nativeClearingL*WPFiniteZSource.R p*
        (-descendedP p+LaurentPolynomial.C (1/3 : ZMod p)*
          ((WPFiniteLVSource.LV p).toLaurent-T (-(((p-1)/2 : ℕ) : ℤ))*
            invert (WPFiniteLVSource.LV p).toLaurent)) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have hu : (2 : (ZMod p)[T;T⁻¹])*LaurentPolynomial.C (1/2 : ZMod p)=1 := by
    change LaurentPolynomial.C (2 : ZMod p)*LaurentPolynomial.C (1/2 : ZMod p)=1
    rw [←map_mul,mul_one_div_cancel h2,map_one]
  have hb := actual_positive_B_cleared p hp
  have hz := actual_original_Z_derivative p hp
  linear_combination LaurentPolynomial.C (1/2 : ZMod p)*hb+
    (nativeClearingL : (ZMod p)[T;T⁻¹])*hz-
    (nativeClearingL*descendedBgamma p hp+nativeClearingGamma*comparisonField p)*hu

/-- This is the printed omega_HF source after clearing, with both actual R carriers distinct. -/
noncomputable def actualPrintedHFNumerator (_hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  let A := (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent
  (3*T 1^2*A^2*(4*T 1-1)-
      LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*A*R*T (-1))*comparisonField p+
    nativeClearingL*A*R*WPFiniteZSource.R p*
      (descendedP p-LaurentPolynomial.C (1/3 : ZMod p)*
        ((WPFiniteLVSource.LV p).toLaurent-T (-(((p-1)/2 : ℕ) : ℤ))*
          invert (WPFiniteLVSource.LV p).toLaurent))

/-- The numerator comes from the original common and balanced carriers, with no source premise. -/
theorem actual_original_HF_attachment (hp : 19≤p) :
    (nativeClearingL : (ZMod p)[T;T⁻¹])*actualOmegaHFNumerator p hp=
      actualPrintedHFNumerator p hp := by
  have hb := actual_Bgamma_Z_cleared p hp
  have hpoly := original_HF_polynomial_clearing (K:=ZMod p)
  unfold actualOmegaHFNumerator actualPrintedHFNumerator
  dsimp only
  have hL : (nativeClearingL : (ZMod p)[T;T⁻¹])=
      2*T 1*(T 1+1)*(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent := rfl
  linear_combination
    -(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*R*hb+
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent*comparisonField p*hpoly+
      delta*comparisonField p*hL

/-- Clearing retains the whole proper, reflected Sigma and period density at the same pole order. -/
theorem actual_original_low_density_cleared (hp : 19≤p) :
    (nativeClearingL : (ZMod p)[T;T⁻¹])*actualOriginalLowDensity p hp=
      3*R^(p-1)*commonHField p*actualPrintedHFNumerator p hp+
      nativeClearingL*((3*R^p*dlogQNumerator*T (-(((p-1)/2 : ℕ) : ℤ)))*
        (LaurentPolynomial.C (1/6 : ZMod p)*actualProperLowNumerator p hp)-
        (LaurentPoleField.fieldAbar p).toLaurent^p*(dlogQNumerator*periodField p hp)) := by
  have h := actual_original_HF_attachment p hp
  unfold actualOriginalLowDensity
  linear_combination 3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*h

end WPFieldAssembly.SourceClosureBalancedHFSource
