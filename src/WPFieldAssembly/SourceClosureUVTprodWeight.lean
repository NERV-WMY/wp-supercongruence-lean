import WPFieldAssembly.SourceClosureUVWholeContraction
import WPFieldAssembly.SourceClosureUVProductWeight

open scoped Polynomial LaurentPolynomial BigOperators
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualKwWeightedTrace WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.ActualUW16PrimitiveSource
  WPFieldAssembly.SourceClosureSigmaKCarry WPFieldAssembly.SourceClosureSigmaGclosed
  WPFieldAssembly.SourceClosureSigmaProperEndpoint
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWeightedK0 WPFieldAssembly.SourceClosureUVWholeContraction
  WPFieldAssembly.SourceClosureUVProductWeight

namespace WPFieldAssembly.SourceClosureUVTprodWeight

set_option maxHeartbeats 1600000

/- The original Tprod is evaluated before its canonical p-hole is paired
   with the same branch scalar. W1 comes from the genuine integral first carry. -/

noncomputable def originalW1Field (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (originalW1Integral p).map (WPPIntegralReduction.residueHom p)

theorem originalW1Field_formula (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalW1Field p =
      Polynomial.C (-2*WPFiniteABSourceTail.epsilon p*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/15)*originalE4CenteredField p :=
  originalW1Integral_field p hp

theorem originalE4Centered_degree (p : ℕ) [Fact p.Prime] :
    (originalE4CenteredField p).natDegree≤(p-1)/2 := by
  have hE : (WPFiniteLVSource.evenSquared p : (ZMod p)[X]).natDegree≤(p-1)/2 := by
    unfold WPFiniteLVSource.evenSquared
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_C_mul_le _ _).trans (by
      rw [natDegree_X_pow]
      have := (Finset.mem_Ico.mp hj).2
      omega)
  have hs : (4*(WPFiniteWSource.squaredCoordinate : (ZMod p)[X])).natDegree≤1 := by
    unfold WPFiniteWSource.squaredCoordinate
    compute_degree
  unfold originalE4CenteredField
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact natDegree_comp_le.trans ((Nat.mul_le_mul hE hs).trans (by omega))
  · simp

theorem originalW1Field_degree (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (originalW1Field p).natDegree≤(p-1)/2 := by
  rw [originalW1Field_formula p hp]
  exact (natDegree_C_mul_le _ _).trans (originalE4Centered_degree p)

theorem originalW1Field_origin (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (originalW1Field p).coeff 0=0 := by
  rw [coeff_zero_eq_eval_zero,originalW1Field_formula p hp]
  simp only [eval_mul,eval_C,originalE4CenteredField,eval_sub,eval_comp,
    eval_ofNat,WPFiniteWSource.squaredCoordinate,eval_add,eval_X,eval_one]
  have hs : (4 : ZMod p)*((5 : ZMod p)⁻¹*(0+1))=4/5 := by ring
  rw [hs,sub_self,mul_zero]

theorem positiveLog_invert (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    invert (ActualKwWeightedTrace.positiveLog p z)=ActualKwWeightedTrace.negativeLog p z := by
  simp only [ActualKwWeightedTrace.positiveLog,ActualKwWeightedTrace.negativeLog,
    map_sum,map_mul,invert_C,invert_T]

theorem negativeLog_invert (p : ℕ) [Fact p.Prime] (z : ZMod p) :
    invert (ActualKwWeightedTrace.negativeLog p z)=ActualKwWeightedTrace.positiveLog p z := by
  simp only [ActualKwWeightedTrace.positiveLog,ActualKwWeightedTrace.negativeLog,
    map_sum,map_mul,invert_C,invert_T,neg_neg]

theorem normEntropyField_invert (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    invert (ActualSigmaNormCarrySource.normEntropyField p)=
      ActualSigmaNormCarrySource.normEntropyField p := by
  rw [normEntropyField_reflected p hp]
  simp only [map_sub,map_mul,map_neg,invert_C,positiveLog_invert,negativeLog_invert]
  ring

theorem originalK1Field_closed (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalK1Field p =
      LaurentPolynomial.C
        (2*((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)))*originalK0 p +
      LaurentPolynomial.C (15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p)+
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
        ActualSigmaNormCarrySource.normEntropyField p := by
  rw [originalK1Field,originalK0Field_identification p hp]
  rfl

theorem originalK1Field_invert (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    invert (originalK1Field p)=originalK1Field p := by
  rw [originalK1Field_closed p hp]
  simp only [map_add,map_mul,invert_C,originalK0_invert,normEntropyField_invert p hp]

/-- The two endpoint values are kept as the actual source's subtracted values. -/
theorem originalTprod_symmetric_source (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    endSym (fourUnitField p hp) (Tprod p) =
      originalK1Field p*((WPFiniteWSource.W p).toLaurent+
        invert (WPFiniteWSource.W p).toLaurent)+
      originalK0 p*((originalW1Field p).toLaurent+invert (originalW1Field p).toLaurent)-
      LaurentPolynomial.C
        (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹ (Tprod p))-
      LaurentPolynomial.C
        (LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp) (Tprod p)) := by
  have hT : Tprod p=originalK1Field p*(WPFiniteWSource.W p).toLaurent+
      originalK0 p*(originalW1Field p).toLaurent := by
    rw [Tprod,originalK0Field_identification p hp,originalW1Field_formula p hp]
    rfl
  have hSym : Tprod p+invert (Tprod p)=
      originalK1Field p*((WPFiniteWSource.W p).toLaurent+
        invert (WPFiniteWSource.W p).toLaurent)+
      originalK0 p*((originalW1Field p).toLaurent+invert (originalW1Field p).toLaurent) := by
    rw [hT]
    simp only [map_add,map_mul,originalK1Field_invert p hp,originalK0_invert]
    ring
  rw [endSym,hSym]

/-- UW18c acts on the complete original product and the actual W1 first carry. -/
theorem originalTprod_whole_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (endSym (fourUnitField p hp) (Tprod p)) =
      -(33/WPFiniteABSourceTail.epsilon p : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))*
          (2*(WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4)+
      (45/WPFiniteABSourceTail.epsilon p : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          ((WPFiniteWSource.W p).eval (1/4)+2*(WPFiniteWSource.W p).eval 4)+
      (2/WPFiniteABSourceTail.epsilon p : ZMod p)*originalWeightedFieldTrace p
        (ActualSigmaNormCarrySource.normEntropyField p*
          ((WPFiniteWSource.W p).toLaurent+invert (WPFiniteWSource.W p).toLaurent))-
      (33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalW1Field p).eval (1/4)+(originalW1Field p).eval 4) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 := pow_ne_zero _ h5
  let S := (WPFiniteWSource.W p : (ZMod p)[X]).toLaurent+
    invert (WPFiniteWSource.W p).toLaurent
  have hWdegree : (WPFiniteWSource.W p : (ZMod p)[X]).natDegree<p :=
    (WPFiniteWSource.W_degree p hp).trans_lt (by omega)
  have hW0 : (WPFiniteWSource.W p : (ZMod p)[X]).coeff 0=0 :=
    WPFiniteWSource.W_origin p
  have hWK : originalWeightedFieldTrace p (originalK0 p*S)=
      -(33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4) := by
    simpa only [S,hW0,mul_zero,add_zero] using
      originalK0_low_symmetric_weight p hp (WPFiniteWSource.W p) hWdegree
  have hWS : originalWeightedFieldTrace p S=
      3*(2*(WPFiniteWSource.W p).eval 4+(WPFiniteWSource.W p).eval (1/4)) := by
    simpa only [S,hW0,mul_zero,sub_zero] using
      original_weight_low_symmetric p hp (WPFiniteWSource.W p) hWdegree
  have hW1degree : (originalW1Field p).natDegree<p :=
    (originalW1Field_degree p hp).trans_lt (by omega)
  have hW1K : originalWeightedFieldTrace p
      (originalK0 p*((originalW1Field p).toLaurent+invert (originalW1Field p).toLaurent))=
      -(33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalW1Field p).eval (1/4)+(originalW1Field p).eval 4) := by
    simpa only [originalW1Field_origin p hp,mul_zero,add_zero] using
      originalK0_low_symmetric_weight p hp (originalW1Field p) hW1degree
  have hK : originalK1Field p*S =
      LaurentPolynomial.C
        (2*((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p)))*(originalK0 p*S)+
      LaurentPolynomial.C (15*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)/
        WPFiniteABSourceTail.epsilon p)*S+
      LaurentPolynomial.C (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
        (ActualSigmaNormCarrySource.normEntropyField p*S) := by
    rw [originalK1Field_closed p hp]
    ring
  rw [originalTprod_symmetric_source p hp]
  change originalWeightedFieldTrace p
    (originalK1Field p*S+originalK0 p*((originalW1Field p).toLaurent+
      invert (originalW1Field p).toLaurent)-LaurentPolynomial.C _-LaurentPolynomial.C _)=_
  rw [hK,weighted_sub,weighted_sub,weighted_add,weighted_add,weighted_add,
    weighted_C_mul,weighted_C_mul,weighted_C_mul,
    hWK,hWS,hW1K,weighted_constant_zero p hp,weighted_constant_zero p hp]
  dsimp only [S]
  field_simp [h2,heps]
  ring

/-- The remaining product term is now the finite original UW18b expression. -/
theorem originalTprod_entropy_evaluated (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    originalWeightedFieldTrace p (endSym (fourUnitField p hp) (Tprod p)) =
      -(33/WPFiniteABSourceTail.epsilon p : ZMod p)*
        ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)-
          (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p))*
          (2*(WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4)+
      (45/WPFiniteABSourceTail.epsilon p : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          ((WPFiniteWSource.W p).eval (1/4)+2*(WPFiniteWSource.W p).eval 4)+
      (2/WPFiniteABSourceTail.epsilon p : ZMod p)*
        (-(3/4 : ZMod p)*WPFiniteField.ell p (16 : ZMod p)*
            ((WPFiniteWSource.W p).eval (1/4)+(WPFiniteWSource.W p).eval 4)+
          (33/2 : ZMod p)*(originalHa p).eval (1/4)+(21/4 : ZMod p)*(originalHa p).eval 4-
          3*(originalHb p).eval (1/4)+(33/4 : ZMod p)*(originalHb p).eval 4+
          (45/2 : ZMod p)*(originalHx p).eval (1/4)-(45/4 : ZMod p)*(originalHx p).eval 4)-
      (33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*(originalW1Field p).eval (1/4)+(originalW1Field p).eval 4) := by
  rw [originalTprod_whole_weight p hp,original_entropy_W_weight p hp]

end WPFieldAssembly.SourceClosureUVTprodWeight
