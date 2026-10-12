import WPFieldAssembly.SourceClosureUVFieldTransport
import WPFieldAssembly.SourceClosureUVUnitEndpoints
import WPFieldAssembly.SourceClosureSigmaActualVS
import WPFieldAssembly.ActualCommonTraceReduction

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.SourceClosureUVDescent
  WPFieldAssembly.SourceClosureUVPrimitiveSource
  WPFieldAssembly.SourceClosureUVPositiveSource
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureUVUnitEndpoints
  WPFieldAssembly.SourceClosureSigmaActualVS
  WPFieldAssembly.ActualCommonTraceReduction
  WPFieldAssembly.ActualKwFieldTrace

namespace WPFieldAssembly.SourceClosureActualUVAttachment

/- The carrier is the original whole Ucan-u0-VS. The actual rational
   p-division is owned by ActualVS; the positive numerator is separately
   identified by FieldTransport. No derivative or endpoint premise is used. -/

variable {K L : Type*} [Field K] [Field L]

theorem evenSquared_transport (f : K →+* L) (p : ℕ) :
    (WPFiniteLVSource.evenSquared p : K[X]).map f=WPFiniteLVSource.evenSquared p := by
  simp only [WPFiniteLVSource.evenSquared,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,map_div₀,map_one,
    map_mul,map_ofNat,map_natCast]

theorem comparisonField_transport (f : K →+* L) (p : ℕ) :
    coefficientMap f (WPFieldAssembly.ActualBalancedTrace.comparisonField p)=
      WPFieldAssembly.ActualBalancedTrace.comparisonField p := by
  simp only [WPFieldAssembly.ActualBalancedTrace.comparisonField,
    WPFieldAssembly.ActualBalancedTrace.movingEvenField,WPFiniteZSource.phase,
    map_mul,map_add,map_sub,map_ofNat,coefficientMap_C,coefficientMap_T,
    coefficientMap_toLaurent,coefficientMap_invert,Polynomial.map_comp,
    deltaE_transport,squaredCoordinate_transport,map_div₀,map_one]

/-- The original comparison is the same whole P plus its reflection, in either prime class. -/
theorem descendedP_actual_comparison (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p) :
    (descendedP p : K[T;T⁻¹])+invert (descendedP p)=
      WPFieldAssembly.ActualBalancedTrace.comparisonField p := by
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have : CharP (AlgebraicClosure K) p := charP_of_injective_ringHom f.injective p
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq (1/5 : AlgebraicClosure K)
    (by decide : 0<(2 : ℕ))
  have h := WPFieldAssembly.ActualBalancedTrace.actual_P_symmetric_comparison
    (K:=AlgebraicClosure K) p hp u hu
  simp only [originalP_descended p hp u hu] at h
  apply coefficientMap_injective_field f
  simpa only [map_add,coefficientMap_invert,descendedP_transport,
    comparisonField_transport] using h

noncomputable def actualUV (p : ℕ) [Fact p.Prime] (hp : 19≤p) : (ZMod p)[T;T⁻¹] :=
  descendedU p-actualVSField p hp

/-- Either original quadratic branch gives the same whole carrier, with the same actual VS. -/
theorem actualUV_original_field (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19≤p)
    (f : ZMod p →+* K) (u : K) (hu : u^2=1/5) :
    coefficientMap f (actualUV p hp)=
      originalU p u-coefficientMap f (actualVSField p hp) := by
  rw [actualUV,map_sub,descendedU_transport f p,originalU_descended (K:=K) p hp u hu]

noncomputable def actualPositiveB (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (ZMod p)[T;T⁻¹] :=
  (R : (ZMod p)[T;T⁻¹])*descendedBgamma p hp

/-- Positive B is attached to the full original numerator, not the rational subtraction B. -/
theorem actualPositiveB_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    4*poleProduct*actualPositiveB p hp=
      (R : (ZMod p)[T;T⁻¹])*descendedPositiveNumerator p := by
  rw [actualPositiveB]
  linear_combination (R : (ZMod p)[T;T⁻¹])*descendedBgamma_source (K:=ZMod p) p hp

/-- This is the actual whole-carrier source equation, not an assumed derivative. -/
theorem actualUV_derivative (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    D (actualUV p hp)=commonSigmaField p hp+descendedBgamma p hp := by
  rw [actualUV,map_sub,descendedU_derivative p hp,actualVSField_derivative_closed p hp]
  unfold commonSigmaField originalAlpha WPFiniteNC122.q originalFrobeniusSource
  rw [show ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 by omega]
  ring

/-- The original branch normalization is preserved by subtracting the SAME actual VS. -/
theorem actualUV_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp)=
      -LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
        (actualVSField p hp) := by
  rw [actualUV,map_sub,descendedU_branch_zero p hp,zero_sub]

/-- Both actual unit ends retain the same full u0 and the actual zero VS endpoints. -/
theorem actualUV_endpoints (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
        (SourceClosureSigmaProperEndpoint.fourUnitField p hp) (actualUV p hp)=
      -(descendedU0 p : ZMod p) ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
        (SourceClosureSigmaProperEndpoint.fourUnitField p hp)⁻¹ (actualUV p hp)=
      -(descendedU0 p : ZMod p) := by
  have hU := descendedUcan_endpoints (K:=ZMod p) p hp
    (SourceClosureSigmaProperEndpoint.fourUnitField p hp) rfl
  have hVS := actualVSField_endpoints p hp
  constructor
  · simp only [actualUV,descendedU,map_sub,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hU.1,hVS.1,zero_sub,sub_zero]
  · simp only [actualUV,descendedU,map_sub,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hU.2,hVS.2,zero_sub,sub_zero]

noncomputable def actualMu (p : ℕ) [Fact p.Prime] (hp : 19≤p) : ZMod p :=
  LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
    (SourceClosureSigmaProperEndpoint.fourUnitField p hp)⁻¹ (actualUV p hp)-
  LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualUV p hp)-
  (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2

/-- UW18's mu is the original endpoint difference, with full u0 and VS branch. -/
theorem actualMu_original_branch (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    actualMu p hp=-(descendedU0 p : ZMod p)+
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ)
        (actualVSField p hp)-
      (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2/2 := by
  rw [actualMu,(actualUV_endpoints p hp).2,actualUV_branch p hp]
  ring

/-- The positive B clears the common R weight without changing its sign or source. -/
theorem actualUV_cleared_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (R : (ZMod p)[T;T⁻¹])*D (actualUV p hp)=
      R*commonSigmaField p hp+actualPositiveB p hp := by
  rw [actualUV_derivative,actualPositiveB,mul_add]

/-- The retained common-trace cancellation now has no free UV derivative hypothesis. -/
theorem actualUV_common_trace_row (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    WPPIntegralReduction.residueHom p
        (WPFieldAssembly.ActualIntegralGreenTrace.commonSourceTraceIntegral p hp)+
      WPFieldAssembly.ActualCommonFieldIBP.kwFieldTrace p
        (D (commonHField p)*actualUV p hp)=
      3*LaurentPoleField.fieldTrace p (p+1)
        ((R : (ZMod p)[T;T⁻¹])^(p-1)*delta*commonHField p*
          WPFieldAssembly.ActualBalancedTrace.comparisonField p)-
      3*LaurentPoleField.fieldTrace p p
        (R^(p-1)*commonHField p*actualPositiveB p hp) := by
  exact actual_commonSourceTrace_cleared_cancellation p hp
    (actualUV p hp) (actualPositiveB p hp) (actualUV_cleared_source p hp)

end WPFieldAssembly.SourceClosureActualUVAttachment
