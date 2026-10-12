import WPFieldAssembly.SourceClosureVbalFieldEvaluation
import WPFieldAssembly.ActualVbalCarry
import WPFieldAssembly.ActualKwRationalRowAttachment
import WPFieldAssembly.SourceClosureVbalArithmetic

namespace WPFieldAssembly.ActualVbalFieldClosure

open WPPIntegralReduction ActualIntegralGreenTrace ActualEntropyFifth
  ActualKwWeightedTrace ActualKwFiniteHBridge ActualKwOrderedEndpoints
  ActualKwRationalRowAttachment WPFiniteField

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- Base change preserves the whole original finite triangular F1 trace. -/
theorem actualTwField_base_change (p : ℕ) [Fact p.Prime] [CharP K p] :
    (ZMod.castHom (dvd_refl p) K) (ActualComparisonF1Attachment.actualTwField p)=
      movingTw (K:=K) p := by
  simp only [ActualComparisonF1Attachment.actualTwField,movingTw,movingMinus,
    movingRplus,movingDend,movingH,WPFiniteLoop.D,WPFiniteLoop.L,finiteLogValue,
    map_add,map_sub,map_mul,map_neg,map_div₀,map_pow,map_inv₀,map_natCast,map_ofNat,
    map_one,map_zero,map_sum]

/-- The actual rational divided value has precisely the full SB103f-g alphabet. -/
theorem actual_vBalanced_field_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (vBalancedDividedIntegral p hp))=
      vbalAlphabet p u w := by
  rw [ActualVbalCarry.actual_vBalanced_field_alphabet_K p hp u hu,
    actualTwField_base_change]
  exact original_field_terms_closed p hp u w hu hw

theorem actual_vBalanced_T5_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (2/3 : K)*(ZMod.castHom (dvd_refl p) K)
      (residueHom p (vBalancedDividedIntegral p hp))+originalT5 p u=
      vbalMomentConsumer p u w := by
  rw [actual_vBalanced_field_closed p hp u w hu hw,vbalAlphabet_T5_consumer p hp]

/-- The original weighted value cancels the conic packet and cubic endpoint
against exactly their retained consumer weights, without assigning a source value. -/
theorem actual_vBalanced_fifth_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (2/3 : K)*(ZMod.castHom (dvd_refl p) K)
      (residueHom p (vBalancedDividedIntegral p hp))+originalT5 p u+
      2*WPFiniteNC122.Aeven p (-(11/5 : K)*u)+(11/15 : K)*conicPacket p u w=
      (2/3 : K)*vbalProduct p u+(23/15 : K)*R p (-2 : K)+
      (22/5 : K)*(WPFiniteNC122.Aeven p (2*u)-WPFiniteNC122.Aeven p u)+
      (4/15 : K)*originalG p (1/5) := by
  rw [actual_vBalanced_field_closed p hp u w hu hw]
  exact vbalAlphabet_fifth_consumer p hp u w

/-- SB101 keeps its actual period, native metric and complete Cauchy field source. -/
theorem actual_SB101_field_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    (ZMod.castHom (dvd_refl p) K) (residueHom p (qStarDividedIntegral p hp))=
      vbalAlphabet p u w-
      (ZMod.castHom (dvd_refl p) K)
        (ActualDeltaUNextSource.QO p (WPActualRankTwoLegendreField.actualLegendreJacobi p^2*
          ActualJointGreen.actualTbarP p))-
      (ZMod.castHom (dvd_refl p) K) (residueHom p (periodCarryIntegral p hp))-
      (1/2 : K)*(ZMod.castHom (dvd_refl p) K)
        (residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp)) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (actual_SB101_field_source p hp)
  simpa only [map_sub,map_mul,map_div₀,map_one,map_ofNat,
    actual_vBalanced_field_closed p hp u w hu hw] using h

/-- The same original SB98-101 carrier feeds the final moment without a scalar assignment. -/
theorem actual_SB98_101_coupled_field_closed (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    3*(ZMod.castHom (dvd_refl p) K)
      (residueHom p (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp))=
      vbalAlphabet p u w-
      (ZMod.castHom (dvd_refl p) K)
        (ActualDeltaUNextSource.QO p (WPActualRankTwoLegendreField.actualLegendreJacobi p^2*
          ActualJointGreen.actualTbarP p))-
      (ZMod.castHom (dvd_refl p) K) (residueHom p (periodCarryIntegral p hp))-
      (1/2 : K)*(ZMod.castHom (dvd_refl p) K)
        (residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp))+
      (ZMod.castHom (dvd_refl p) K) (residueHom p (commonSourceTraceIntegral p hp))+
      (ZMod.castHom (dvd_refl p) K) (residueHom p (balancedTraceIntegral p hp)) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (actual_coupled_trace_field_source p hp)
  simpa only [map_add,map_mul,map_ofNat,actual_SB101_field_closed p hp u w hu hw] using h

/-- The same coupled trace feeds the original T5 consumer with every actual carrier. -/
theorem actual_SB98_101_T5_consumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (u w : K) (hu : u^2=(1/5 : K)) (hw : w^2=(3/11 : K)) :
    2*(ZMod.castHom (dvd_refl p) K)
      (residueHom p (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp))+
      (2/3 : K)*(ZMod.castHom (dvd_refl p) K)
        (ActualDeltaUNextSource.QO p (WPActualRankTwoLegendreField.actualLegendreJacobi p^2*
          ActualJointGreen.actualTbarP p))+
      (2/3 : K)*(ZMod.castHom (dvd_refl p) K) (residueHom p (periodCarryIntegral p hp))+
      (1/3 : K)*(ZMod.castHom (dvd_refl p) K)
        (residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp))-
      (2/3 : K)*(ZMod.castHom (dvd_refl p) K) (residueHom p (commonSourceTraceIntegral p hp))-
      (2/3 : K)*(ZMod.castHom (dvd_refl p) K) (residueHom p (balancedTraceIntegral p hp))+
      originalT5 p u=vbalMomentConsumer p u w := by
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc := actual_SB98_101_coupled_field_closed (K:=K) p hp u w hu hw
  rw [←vbalAlphabet_T5_consumer p hp u w]
  field_simp [h2,h3] at hc ⊢
  linear_combination hc

end WPFieldAssembly.ActualVbalFieldClosure
