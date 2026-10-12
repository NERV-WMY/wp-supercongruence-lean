import WPFieldAssembly.SourceClosureBalancedNativeNormalization
import WPFieldAssembly.SourceClosureUVWholeContraction

open scoped LaurentPolynomial
open LaurentPolynomial WPFieldAssembly.ActualKwFieldTrace
  WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace
  WPFieldAssembly.SourceClosureUVWeightedBands
  WPFieldAssembly.SourceClosureUVWeightedLog
  WPFieldAssembly.SourceClosureUVWholeContraction
  WPFieldAssembly.SourceClosureBalancedNativeNormalization

namespace WPFieldAssembly.SourceClosureBalancedHomogeneousTrace

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/-- The first homogeneous phase retains the original canonical-hole weight. -/
theorem actual_first_phase_weight (hp : 19≤p) :
    originalWeightedFieldTrace p (T (p : ℤ)+T (-(p : ℤ)))=99/4 := by
  have h := originalPhi_weight p hp
  change originalWeightedFieldTrace p
    ((T (p : ℤ)+T (-(p : ℤ)))-LaurentPolynomial.C (17/4 : ZMod p))=99/4 at h
  rw [weighted_sub,weighted_constant_zero p hp,sub_zero] at h
  exact h

/-- Clearing the entire A^p denominator retains the second Frobenius band. -/
theorem actual_positive_second_phase_weight (hp : 19≤p) :
    originalWeightedFieldTrace p (T (2*(p : ℤ)))=2133/16 := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p)≠0 := by
    rw [show (16 : ZMod p)=4*4 by ring]
    exact mul_ne_zero h4 h4
  let d : (ZMod p)[T;T⁻¹] := 3*T (-1)*(4-11*T 1)
  have hclear : LaurentPoleField.fieldTrace p (p+1)
      ((LaurentPoleField.fieldAbar p).toLaurent^p*(d*T (2*(p : ℤ))))=
        fieldDlogQ p (T (2*(p : ℤ))) := by
    change LaurentPoleField.fieldTrace p (p+1)
      ((LaurentPoleField.fieldAbar p).toLaurent^p*(d*T (2*(p : ℤ))))=
        LaurentPoleField.fieldTrace p 1 (d*T (2*(p : ℤ)))
    simpa only [Nat.add_comm] using
      LaurentPoleField.fieldTrace_cleared_pow p 1 p hp (d*T (2*(p : ℤ)))
  have hhigh : LaurentPoleField.fieldTrace p (p+1) (d*T (3*(p : ℤ)))=33/16 := by
    have h := original_top_weights p hp
    rw [show d*T (3*(p : ℤ))=
      3*T (-1)*(4-11*T 1)*(LaurentPolynomial.C (1 : ZMod p)*T (3*(p : ℤ))) by
        simp only [d,map_one,one_mul]]
    rw [literal_density_monomial,map_sub,LaurentPoleField.fieldTrace_monomial,
      LaurentPoleField.fieldTrace_monomial,h.1,h.2]
    ring
  have hlow : LaurentPoleField.fieldTrace p (p+1) (d*T (2*(p : ℤ)))=0 := by
    simpa only [d,map_one,one_mul] using
      dlog_high_pole_vanish p (2*(p : ℤ)) (by omega) (1 : ZMod p)
  have hend : fieldDlogQ p (T (2*(p : ℤ)))=-(513/16 : ZMod p) := by
    rw [show (T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1 : ZMod p)*T (2*(p : ℤ)) by simp,
      fieldDlogQ_monomial p hp,endpointWeight,if_pos (by omega)]
    rw [show (2*(p : ℤ)).toNat=2*p by omega,Nat.mul_comm 2 p,pow_mul,pow_mul,
      ZMod.pow_card,ZMod.pow_card]
    field_simp [h4,h16]
    ring
  have ht : (T (p : ℤ)*T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=T (3*(p : ℤ)) := by
    rw [←T_add]
    congr 1
    ring
  unfold originalWeightedFieldTrace
  rw [original_weight_numerator_split]
  rw [show ((-3*(LaurentPoleField.fieldAbar p).toLaurent^p+18*T (p : ℤ)-12)*
      (3*T (-1)*(4-11*T 1)))*T (2*(p : ℤ))=
      LaurentPolynomial.C (-3 : ZMod p)*
        ((LaurentPoleField.fieldAbar p).toLaurent^p*(d*T (2*(p : ℤ))))+
      LaurentPolynomial.C (18 : ZMod p)*(d*T (3*(p : ℤ)))-
      LaurentPolynomial.C (12 : ZMod p)*(d*T (2*(p : ℤ))) by
        dsimp only [d]
        simp only [map_neg,map_ofNat]
        linear_combination 18*(3*T (-1)*(4-11*T 1))*ht]
  rw [map_sub,map_add,fieldTrace_C_mul,fieldTrace_C_mul,fieldTrace_C_mul,
    hclear,hhigh,hlow,hend]
  ring

theorem actual_second_phase_weight (hp : 19≤p) :
    originalWeightedFieldTrace p (T (2*(p : ℤ))+T (-2*(p : ℤ)))=2133/16 := by
  rw [weighted_add,actual_positive_second_phase_weight p hp,
    show (T (-2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=
      LaurentPolynomial.C (1 : ZMod p)*T (-2*(p : ℤ)) by simp,
    weighted_nonpositive p hp _ (by omega),add_zero]

/-- The specified actual homogeneous correction has precisely its original consumer weight. -/
theorem actual_homogeneous_trace_correction (hp : 19≤p) :
    (1/9 : ZMod p)*originalWeightedFieldTrace p (actualNativeHomogeneousR p hp)=
      (66/25 : ZMod p)*(SourceClosureActualUVAttachment.actualMu p hp+
        actualBalancedBranchB p)+(207/4 : ZMod p)*
          SourceClosureBalancedNativeBetaIdentification.actualOriginalBeta p := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2
    (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3
    (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h9 : (9 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 9
    (by omega) (by omega)
  have h16 : (16 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 16
    (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  unfold actualNativeHomogeneousR
  simp only [weighted_add,weighted_C_mul,weighted_constant_zero p hp,
    actual_first_phase_weight p hp,actual_second_phase_weight p hp]
  field_simp [h2,h3,h4,h5,h9,h16,h25]
  ring

end WPFieldAssembly.SourceClosureBalancedHomogeneousTrace
