import WPFieldAssembly.ActualIntegralGreenTrace
import WPFieldAssembly.ActualKwFieldTrace
import WPFieldAssembly.ActualCommonFieldIBP

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPPIntegralReduction WPActualEtaIntegrality
  WPFieldAssembly.ActualHFTransmutation WPFieldAssembly.ActualSB101Trace
  WPFieldAssembly.ActualGreenCommonTrace WPFieldAssembly.ActualBalancedGreenTransfer
  WPFieldAssembly.ActualBalancedTrace WPFieldAssembly.ActualSigmaIntegral
  WPFieldAssembly.ActualIntegralGreenTrace WPFieldAssembly.ActualKwFieldTrace

namespace WPFieldAssembly.ActualCommonTraceReduction

set_option maxHeartbeats 1600000

noncomputable def greenHAtIntegral (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (integralRationals p)[T;T⁻¹] :=
  invert (((ActualGreenPrimitive.greenHIntegral p hp).comp
    (WPHasseIntegralTransport.integralV p (by omega))).toLaurent)

theorem greenHAtIntegral_rational (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (greenHAtIntegral p hp)=greenHAtQ p hp := by
  simp only [greenHAtIntegral,greenHAtQ,WPActualChiSource.coefficientMap_invert,
    WPActualChiSource.coefficientMap_toLaurent,Polynomial.map_comp,
    WPHasseIntegralTransport.integralV_map_rational,ActualGreenPrimitive.greenHq]

/-- The original low Green primitive reduces to the unchanged native H pullback. -/
theorem greenHAtIntegral_field (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPActualChiSource.coefficientMap (residueHom p) (greenHAtIntegral p hp)=
      invert ((WPActualConicInfinitySource.nativeHField p).comp
        (WPHasseIntegralTransport.fieldV p)).toLaurent := by
  simp only [greenHAtIntegral,WPActualChiSource.coefficientMap_invert,
    WPActualChiSource.coefficientMap_toLaurent,Polynomial.map_comp,
    ActualGreenPrimitive.greenHIntegral_field_native,
    WPHasseIntegralTransport.integralV_map_field]
  rfl

noncomputable def commonHField (p : ℕ) [Fact p.Prime] : (ZMod p)[T;T⁻¹] :=
  invert ((WPActualConicInfinitySource.nativeHField p).comp
    (WPHasseIntegralTransport.fieldV p)).toLaurent

noncomputable def commonSigmaField (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (residueHom p) (actualSigmaIntegral p hp)

theorem commonProducts_reduce (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    reduceLaurent p (greenHAtQ p hp*actualSigmaQ p hp)=
      commonHField p*commonSigmaField p hp ∧
    reduceLaurent p (greenHAtQ p hp*comparisonRational p hp)=
      commonHField p*comparisonField p := by
  constructor
  · rw [←greenHAtIntegral_rational p hp,←actualSigmaIntegral_value p hp,
      ←map_mul,reduce_integral_map,map_mul,greenHAtIntegral_field]
    rfl
  · rw [←greenHAtIntegral_rational p hp,comparisonRational,
      ←map_mul,reduce_integral_map,map_mul,greenHAtIntegral_field,
      comparisonIntegral_field p hp]
    rfl

theorem kwNumeratorQ_helper (p : ℕ) : kwNumeratorQ p=rationalKw p := rfl

/-- The original logarithmic trace uses the complete divided derivative numerator. -/
theorem kwLogNumeratorQ_helper (p : ℕ) (hp : 0<p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent*kwDerivativeNumeratorQ p-
      kwNumeratorQ p*D (WPFiniteZSource.Abar : ℚ[X]).toLaurent =
        rationalKwDlog p := by
  have h := rationalKw_derivative_division p hp
  rw [←kwNumeratorQ_helper,kwNumerator_derivative p hp,pole_Abar_eq] at h
  have hpq : (p : ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hi : LaurentPolynomial.C (1/(p : ℚ))*LaurentPolynomial.C (p : ℚ)=
      (1 : ℚ[T;T⁻¹]) := by
    rw [←map_mul,one_div_mul_cancel hpq,map_one]
  calc
    _ = LaurentPolynomial.C (1/(p : ℚ))*(LaurentPolynomial.C (p : ℚ)*
        ((WPFiniteZSource.Abar : ℚ[X]).toLaurent*kwDerivativeNumeratorQ p-
          kwNumeratorQ p*D (WPFiniteZSource.Abar : ℚ[X]).toLaurent)) := by
      rw [←mul_assoc,hi,one_mul]
    _ = LaurentPolynomial.C (1/(p : ℚ))*(LaurentPolynomial.C (p : ℚ)*
        rationalKwDlog p) := by
      congr 1
      linear_combination h
    _ = _ := by rw [←mul_assoc,hi,one_mul]

theorem kwTraceQ_helper (p : ℕ) (L : ℚ[T;T⁻¹]) :
    kwTraceQ p L=LaurentPoleTrace.trace p (rationalKw p*L) := rfl

theorem kwLogTraceQ_helper (p : ℕ) (hp : 0<p) (L : ℚ[T;T⁻¹]) :
    kwLogTraceQ p L=LaurentPoleTrace.trace (p+1) (rationalKwDlog p*L) := by
  change LaurentPoleTrace.trace (p+1)
    (((WPFiniteZSource.Abar : ℚ[X]).toLaurent*kwDerivativeNumeratorQ p-
      kwNumeratorQ p*D (WPFiniteZSource.Abar : ℚ[X]).toLaurent)*L)=_
  rw [kwLogNumeratorQ_helper p hp]

/-- Reduction of the entire integral Kw source, with all signed Cartier slots. -/
theorem actual_kwTrace_residue (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : ℚ[T;T⁻¹]) (hL : L∈integralLaurent p) :
    residueHom p ⟨kwTraceQ p L,kwTrace_integral p hp L hL⟩=
      3*LaurentPoleField.fieldTrace p 1
        ((R : (ZMod p)[T;T⁻¹])*
          WPFiniteCartier.cartier p (Fact.out : p.Prime).pos (reduceLaurent p L)) := by
  change ((kwTraceQ p L : ℚ) : ZMod p)=_
  rw [kwTraceQ_helper]
  exact actualKw_trace_reduce p hp L hL

/-- The full logarithmic trace retains its p+1 denominator until field reduction. -/
theorem actual_kwLogTrace_residue (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (L : ℚ[T;T⁻¹]) (hL : L∈integralLaurent p) :
    residueHom p ⟨kwLogTraceQ p L,kwLogTrace_integral p hp L hL⟩=
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*reduceLaurent p L) := by
  change ((kwLogTraceQ p L : ℚ) : ZMod p)=_
  rw [kwLogTraceQ_helper p (by omega)]
  have h := actualKwDlog_trace_reduce p hp L hL
  rw [←field_A,←delta_derivative] at h
  exact h

/-- NC117's actual common-source term, without deleting either full Laurent source. -/
theorem actual_commonSourceTrace_residue (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)=
      3*LaurentPoleField.fieldTrace p 1
        ((R : (ZMod p)[T;T⁻¹])*WPFiniteCartier.cartier p (Fact.out : p.Prime).pos
          (reduceLaurent p (greenHAtQ p hp*actualSigmaQ p hp)))+
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*
          reduceLaurent p (greenHAtQ p hp*comparisonRational p hp)) := by
  have hH := greenHAtQ_integral p hp
  have hSigma := (integralLaurent p).mul_mem hH (actualSigmaQ_integral p hp)
  have hS : greenHAtQ p hp*comparisonRational p hp∈integralLaurent p :=
    (integralLaurent p).mul_mem hH (mapped_integral p (comparisonIntegral p))
  have he : commonSourceTraceIntegral p hp=
      (⟨kwTraceQ p (greenHAtQ p hp*actualSigmaQ p hp),
        kwTrace_integral p hp _ hSigma⟩ : integralRationals p)+
      ⟨kwLogTraceQ p (greenHAtQ p hp*comparisonRational p hp),
        kwLogTrace_integral p hp _ hS⟩ := by
    apply Subtype.ext
    rfl
  rw [he,map_add,actual_kwTrace_residue p hp _ hSigma,
    actual_kwLogTrace_residue p hp _ hS]

/-- Both complete common sources are attached to their canonical native reductions. -/
theorem actual_commonSourceTrace_canonical (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    residueHom p (commonSourceTraceIntegral p hp)=
      ActualCommonFieldIBP.kwFieldTrace p (commonHField p*commonSigmaField p hp)+
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*commonHField p*comparisonField p) := by
  rw [actual_commonSourceTrace_residue p hp,(commonProducts_reduce p hp).1,
    (commonProducts_reduce p hp).2,ActualCommonFieldIBP.kwFieldTrace_cartier p hp]
  congr 2
  ring

/-- The source hypothesis is the full UV derivative relation, with sigma unchanged. -/
theorem actual_commonSourceTrace_cancellation (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (U B : (ZMod p)[T;T⁻¹]) (hU : D U=commonSigmaField p hp+B) :
    residueHom p (commonSourceTraceIntegral p hp)+
      ActualCommonFieldIBP.kwFieldTrace p (D (commonHField p)*U)=
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*commonHField p*comparisonField p)-
      ActualCommonFieldIBP.kwFieldTrace p (commonHField p*B) := by
  rw [actual_commonSourceTrace_canonical p hp]
  exact ActualCommonFieldIBP.common_sigma_cancellation p hp _ U _ B hU _

/-- Clearing R preserves the original 11/4 pole until the full Kw weight cancels it. -/
theorem actual_commonSourceTrace_cleared_cancellation (p : ℕ) [Fact p.Prime]
    (hp : 19≤p) (U B : (ZMod p)[T;T⁻¹])
    (hU : (R : (ZMod p)[T;T⁻¹])*D U=
      R*commonSigmaField p hp+B) :
    residueHom p (commonSourceTraceIntegral p hp)+
      ActualCommonFieldIBP.kwFieldTrace p (D (commonHField p)*U)=
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*commonHField p*comparisonField p)-
      3*LaurentPoleField.fieldTrace p p (R^(p-1)*commonHField p*B) := by
  have hpow : (R : (ZMod p)[T;T⁻¹])^p=R^(p-1)*R := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1≤p)]
  have hs : (3*(R : (ZMod p)[T;T⁻¹])^p)*(commonHField p*D U)=
      (3*R^p)*(commonHField p*commonSigmaField p hp)+
        3*(R^(p-1)*commonHField p*B) := by
    rw [hpow]
    linear_combination 3*(R : (ZMod p)[T;T⁻¹])^(p-1)*commonHField p*hU
  have ht := congrArg (LaurentPoleField.fieldTrace p p) hs
  rw [map_add,fieldTrace_three_mul] at ht
  change ActualCommonFieldIBP.kwFieldTrace p (commonHField p*D U)=
    ActualCommonFieldIBP.kwFieldTrace p (commonHField p*commonSigmaField p hp)+
      3*LaurentPoleField.fieldTrace p p (R^(p-1)*commonHField p*B) at ht
  have h := ActualCommonFieldIBP.kwFieldTrace_IBP p hp (commonHField p) U
  rw [actual_commonSourceTrace_canonical p hp]
  linear_combination h-ht

end WPFieldAssembly.ActualCommonTraceReduction
