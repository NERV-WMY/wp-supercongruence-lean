import WPFieldAssembly.ActualBalancedTrace
import WPFieldAssembly.ActualSB72Attachment
import WPFieldAssembly.LaurentPoleField

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen
  WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2200000

/- The original period carrier is transported after its rational p-division.
   The full logarithm, anti-reflection and 2p origin shift are retained. -/

namespace WPFieldAssembly.SourceClosureCommonWholeSource

noncomputable def dlogQNumerator {K : Type*} [CommRing K] : K[T;T⁻¹] :=
  3*T (-1)*(4-11*T 1)

theorem dlogQNumerator_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) : coefficientMap f (dlogQNumerator : K[T;T⁻¹])=dlogQNumerator := by
  simp only [dlogQNumerator,map_mul,map_sub,map_ofNat,coefficientMap_T]

noncomputable def periodSourceIntegral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (integralRationals p)[T;T⁻¹] :=
  T (-(((p-1)/2 : ℕ) : ℤ))*actualReflectionDefectIntegral p hp*
    (finiteConicLogIntegral p hp).toLaurent

noncomputable def periodField (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] := coefficientMap (residueHom p) (periodSourceIntegral p hp)

end WPFieldAssembly.SourceClosureCommonWholeSource

namespace WPFieldAssembly.SourceClosureBalancedNativeReciprocal

variable (p : ℕ) [Fact p.Prime]

/-- The original rational p-division preserves its weighted anti-reflection. -/
theorem actual_defect_weighted_anti_field (hp : 19≤p) :
    let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
    T (((p-1)/2 : ℕ) : ℤ)*invert delta=-delta := by
  have hi := weightedReflectionDifference_anti ((p-1)/2)
    ((NativeOriginalResidues.squareQIntegral p hp).comp
      (WPHasseIntegralTransport.integralV p (by omega))).toLaurent
  change actualLowReflectionNumeratorIntegral p hp+
    T (((p-1)/2 : ℕ) : ℤ)*invert (actualLowReflectionNumeratorIntegral p hp)=0 at hi
  rw [actual_low_reflection_defect_source p hp] at hi
  simp only [map_mul,invert_C] at hi
  have hpI : (p : integralRationals p)≠0 := by
    intro hz
    have hq := congrArg Subtype.val hz
    exact (show (p : ℚ)≠0 by positivity) hq
  have hpC : LaurentPolynomial.C (p : integralRationals p)≠0 := by
    intro hz
    apply hpI
    have he := congrArg (fun L : (integralRationals p)[T;T⁻¹] => L.coeff 0) hz
    simpa only [LaurentPolynomial.C_apply,if_true,
      AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using he
  have hz : actualReflectionDefectIntegral p hp+
      T (((p-1)/2 : ℕ) : ℤ)*invert (actualReflectionDefectIntegral p hp)=0 := by
    apply mul_left_cancel₀ hpC
    rw [mul_zero]
    linear_combination hi
  have he := congrArg (coefficientMap (residueHom p)) hz
  simp only [map_add,map_mul,map_zero,coefficientMap_T,coefficientMap_invert] at he
  linear_combination he

end WPFieldAssembly.SourceClosureBalancedNativeReciprocal

namespace WPFieldAssembly.SourceClosureHFNativeTransport

/-- The original rational reflection defect reduces to the actual SB72 polynomial. -/
theorem actual_reflection_defect_native (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (WPPIntegralReduction.residueHom p)
      (actualReflectionDefectIntegral p hp) = (actualDeltaField p hp).toLaurent := by
  rw [actual_reflection_defect_field p hp, actual_chi_Sigma_Taylor p hp]
  unfold weightedReflectionDifference
  ring

/-- SB101's full nonzero-end conic logarithm is LV minus its original q2 shift. -/
theorem actual_period_log_native (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((WPFieldAssembly.ActualJointGreen.finiteConicLogIntegral p hp).map
      (WPPIntegralReduction.residueHom p)).toLaurent =
        (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p) := by
  have h5 : (5 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h125 : (125 : ZMod p) ≠ 0 := by
    rw [show (125 : ZMod p) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hc : (125 : (ZMod p)[X]) * Polynomial.C ((125 : ZMod p)⁻¹) = 1 := by
    change Polynomial.C (125 : ZMod p) * Polynomial.C ((125 : ZMod p)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ h125, map_one]
  have hVP : (WPFiniteNC122Residue.VP : (ZMod p)[X]) =
      WPHasseIntegralTransport.fieldV p := by
    rw [← WPFieldAssembly.ActualLowEuler.Qrev_eq_fieldV p,
      WPFiniteNC122Residue.Qrev_factored, WPFiniteNC122Residue.VP]
    ring
  have hV : (WPFiniteLVSource.V : (ZMod p)[X]) =
      1 - WPHasseIntegralTransport.fieldV p := by
    rw [← hVP]
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr h125)
    change (125 : (ZMod p)[X]) * WPFiniteLVSource.V =
      125 * (1 - WPFiniteNC122Residue.VP)
    rw [WPFiniteLVSource.V_numerator p hp, WPFiniteNC122Residue.VP]
    linear_combination (4 - X) * (4 * X - 1) ^ 2 * hc
  have he : (WPFieldAssembly.ActualJointGreen.finiteConicLogIntegral p hp).map
      (WPPIntegralReduction.residueHom p) =
        (WPFiniteLVSource.evenSquared p : (ZMod p)[X]).comp WPFiniteLVSource.V := by
    simp only [WPFieldAssembly.ActualJointGreen.finiteConicLogIntegral,
      Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
      WPFieldAssembly.ActualJointGreen.finiteEvenSquaredIntegral_field p hp,
      WPHasseIntegralTransport.integralV_map_field]
    rw [hV]
  rw [he, WPFiniteLVSource.LV, map_add, Polynomial.toLaurent_C]
  ring

/-- Direct inversion keeps the actual anti-reflection sign and the full finite log. -/
theorem actual_period_invert (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    invert (SourceClosureCommonWholeSource.periodField p hp) =
      -coefficientMap (WPPIntegralReduction.residueHom p)
        (actualReflectionDefectIntegral p hp) *
      (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)) := by
  have ha := SourceClosureBalancedNativeReciprocal.actual_defect_weighted_anti_field p hp
  dsimp only at ha
  simp only [SourceClosureCommonWholeSource.periodField,
    SourceClosureCommonWholeSource.periodSourceIntegral, map_mul,
    coefficientMap_T, coefficientMap_toLaurent]
  rw [actual_period_log_native p hp]
  simp only [invert_T, neg_neg, map_sub, invert_C]
  linear_combination
    (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
      LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)) * ha

/-- The original period pole has precisely the full 2p origin shift used by the HF source. -/
theorem actual_period_origin_numerator (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.C (2/3 : ZMod p) * T (2 * (p : ℤ)) *
      invert ((LaurentPoleField.fieldAbar p).toLaurent ^ p *
        (SourceClosureCommonWholeSource.dlogQNumerator *
          SourceClosureCommonWholeSource.periodField p hp)) =
    LaurentPolynomial.C (2/3 : ZMod p) *
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * (33 - 12 * T 1) *
      coefficientMap (WPPIntegralReduction.residueHom p)
        (actualReflectionDefectIntegral p hp) *
      (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)) := by
  have hA : LaurentPoleField.fieldAbar p = (WPFiniteZSource.Abar : (ZMod p)[X]) := by
    unfold LaurentPoleField.fieldAbar WPFiniteZSource.Abar
    ring
  have hQ : invert (SourceClosureCommonWholeSource.dlogQNumerator :
      (ZMod p)[T;T⁻¹]) = -(33 - 12 * T 1) := by
    simp only [SourceClosureCommonWholeSource.dlogQNumerator, map_mul, map_sub,
      map_ofNat, invert_T, neg_neg]
    have ht : (T 1 * T (-1) : (ZMod p)[T;T⁻¹]) = 1 := by
      rw [← T_add, add_neg_cancel, T_zero]
    linear_combination -33 * ht
  have ht : (T (2 * (p : ℤ)) * T (-2) ^ p : (ZMod p)[T;T⁻¹]) = 1 := by
    rw [T_pow, ← T_add]
    have he : 2*(p : ℤ)+(p : ℤ)*(-2)=0 := by ring
    simpa only [nsmul_eq_mul] using
      (congrArg (fun n : ℤ => (T n : (ZMod p)[T;T⁻¹])) he).trans T_zero
  rw [hA]
  simp only [map_mul, map_pow, WPFiniteZSource.invert_Abar, mul_pow, hQ,
    actual_period_invert p hp]
  calc
    _ = LaurentPolynomial.C (2/3 : ZMod p) *
        (T (2 * (p : ℤ)) * T (-2) ^ p) *
        (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * (33 - 12 * T 1) *
        coefficientMap (WPPIntegralReduction.residueHom p)
          (actualReflectionDefectIntegral p hp) *
        (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
          LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)) := by ring
    _ = _ := by rw [ht]; ring

/-- The attached actual SB72 defect supplies exactly IR63's two native period rows. -/
theorem actual_period_native_rows (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.C (2/3 : ZMod p) * T (2 * (p : ℤ)) *
      invert ((LaurentPoleField.fieldAbar p).toLaurent ^ p *
        (SourceClosureCommonWholeSource.dlogQNumerator *
          SourceClosureCommonWholeSource.periodField p hp)) =
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * (33 - 12 * T 1) *
      ((NativeChiFieldSource.halfPullbackField p hp).toLaurent *
        (LaurentPolynomial.C (2/3 : ZMod p) * (Dstar p : (ZMod p)[X]).toLaurent *
          (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
            LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p))) +
        (WPFieldAssembly.ActualFirstGreen.CB p).toLaurent *
          (LaurentPolynomial.C (-10/9 : ZMod p) *
            (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
              LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)))) := by
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 := by
    rw [show (9 : ZMod p) = 3 ^ 2 by ring]
    exact pow_ne_zero _ h3
  have hc : (2/3 : ZMod p) * (5/3 : ZMod p) = -(-10/9 : ZMod p) := by
    field_simp [h3, h9]
    ring
  have hC := congrArg (LaurentPolynomial.C : ZMod p → (ZMod p)[T;T⁻¹]) hc
  simp only [map_mul, map_neg] at hC
  rw [actual_period_origin_numerator p hp, actual_reflection_defect_native p hp,
    actual_SB72_ZMod p hp]
  simp only [map_sub, map_mul, Polynomial.toLaurent_C]
  linear_combination
    -(WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p * (33 - 12 * T 1) *
      (WPFieldAssembly.ActualFirstGreen.CB p).toLaurent *
      (invert (WPFiniteLVSource.LV p : (ZMod p)[X]).toLaurent -
        LaurentPolynomial.C (WPFiniteNC122.q p : ZMod p)) * hC

end WPFieldAssembly.SourceClosureHFNativeTransport
