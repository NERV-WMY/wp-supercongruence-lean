import WPFieldAssembly.SourceClosureBalancedNativeKernel
import WPFieldAssembly.SourceClosureLaurentBranchJets

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.SourceClosureBalancedFirstSource
  WPFieldAssembly.SourceClosureBalancedNativeParticular
  WPFieldAssembly.SourceClosureBalancedNativeReflection
  WPFieldAssembly.SourceClosureBalancedNativeForcing
  WPFieldAssembly.SourceClosureBalancedUVSource
  WPFieldAssembly.SourceClosureActualUVAttachment
  WPFieldAssembly.SourceClosureUVFieldTransport
  WPFieldAssembly.SourceClosureLaurentBranchJets

namespace WPFieldAssembly.SourceClosureBalancedNativeBranch

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

theorem actual_CB_three_branch_jets_field (hp : 19≤p) :
    ThreeBranchJets (WPFieldAssembly.ActualFirstGreen.CB p).toLaurent := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hc := (WPFieldAssembly.ActualFirstGreen.actual_carrier_pullbacks p hp).1
  change (WPFieldAssembly.ActualFirstGreen.CB p).comp (5*X^2-1)=
    Polynomial.C (1/5 : ZMod p)*X^p*(WPFieldAssembly.ActualFirstGreen.B p).comp (4*X^3-3*X) at hc
  exact three_branch_jets_toLaurent (WPFieldAssembly.ActualFirstGreen.CB p)
    (WPFieldAssembly.SourceClosureVbalNativePrimitive.conic_carrier_three_branch_jets
      p hp h2 h3 h5 (WPFieldAssembly.ActualFirstGreen.CB p)
      ((WPFieldAssembly.ActualFirstGreen.B p).comp (4*X^3-3*X))
      (1/5 : ZMod p) hc)

theorem actual_native_G_three_branch_jets (hp : 19≤p) :
    ThreeBranchJets (coefficientMap (residueHom p) (nativeProperGIntegral p hp)) := by
  rw [actual_native_G_field p hp]
  exact three_branch_jets_mul _ _ (actual_CB_three_branch_jets_field p hp)

theorem actual_local_proper_three_branch_jets (hp : 19≤p) :
    ThreeBranchJets (actualLocalProperParticular p hp) := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hH : ThreeBranchJets (actualProperPrimitiveCarrier p hp).toLaurent :=
    three_branch_jets_toLaurent (actualProperPrimitiveCarrier p hp)
    (WPFieldAssembly.SourceClosureVbalNativePrimitive.conic_carrier_three_branch_jets
      p hp h2 h3 h5 (actualProperPrimitiveCarrier p hp)
      ((WPFieldAssembly.SourceClosureVbalNativePrimitive.actualNativeProperPrimitive p hp).comp
        (4*X^3-3*X))
      (1/5 : ZMod p) (actual_proper_primitive_carrier_conic p hp))
  exact three_branch_jets_mul (ActualChiEndpoints.zeta p)
    (actualProperPrimitiveCarrier p hp).toLaurent hH

theorem actual_whole_proper_three_branch_jets (hp : 19≤p) :
    ThreeBranchJets (actualWholeProperParticular p hp) := by
  have hH := actual_local_proper_three_branch_jets p hp
  exact three_branch_jets_add _ _ hH
    (three_branch_jets_mul _ _ (three_branch_jets_invert _ hH))

/-- The original P branch vanishes; the entire comparison and invisible phases are retained. -/
theorem actual_P_branch_zero (hp : 19≤p) : branchEval (descendedP p : (ZMod p)[T;T⁻¹])=0 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hdelta : (WPFiniteWSource.deltaE p : (ZMod p)[X]).eval 0=0 := by
    unfold WPFiniteWSource.deltaE
    simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j≠0 := by have := (Finset.mem_Ico.mp hj).1; omega
    rw [zero_pow hj0,mul_zero]
  have hcoord : (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).eval (-1)=0 := by
    simp only [WPFiniteWSource.squaredCoordinate,eval_mul,eval_C,eval_add,
      eval_X,eval_one,neg_add_cancel,mul_zero]
  have hMoving : branchEval (movingEvenField p : (ZMod p)[X]).toLaurent=0 := by
    rw [branch_eval_toLaurent,movingEvenField,eval_comp,hcoord,hdelta]
  have hS : branchEval (comparisonField p : (ZMod p)[T;T⁻¹])=0 := by
    rw [comparisonField,map_mul,map_mul,map_add,branch_eval_invert,hMoving,add_zero,mul_zero]
  have he := congrArg (branchEval (K:=ZMod p)) (descendedP_actual_comparison p hp)
  rw [map_add,branch_eval_invert,hS] at he
  have hz : (2 : ZMod p)*branchEval (descendedP p)=0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left h2

/-- Both prime classes use the value or first jet of the actual multiplier. -/
theorem actual_native_ratio_branch_value (hp : 19≤p) (R : (ZMod p)[T;T⁻¹])
    (hfactor : actualNativeClearedNumerator p hp-
      6*(NativeChiFieldSource.halfPullbackField p hp).toLaurent*actualBalancedField p hp=
        (NativeChiFieldSource.halfPullbackField p hp).toLaurent^2*R) :
    branchEval R=12*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2+
      9*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let G := coefficientMap (residueHom p) (nativeProperGIntegral p hp)
  let delta := coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
  let q : ZMod p := WPFiniteInversion.integerFermatQuotient p 2
  let r : ZMod p := WPFiniteInversion.integerFermatQuotient p 3
  let b := -2*q^2-(3/2 : ZMod p)*q*r
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have hf : branchEval f≠0 ∨ branchEval (D f)≠0 := by
    change branchEval (NativeChiFieldSource.halfPullbackField p hp).toLaurent≠0 ∨
      branchEval (D (NativeChiFieldSource.halfPullbackField p hp).toLaurent)≠0
    rw [branch_eval_toLaurent,D_toLaurent,branch_eval_toLaurent]
    exact actual_balanced_branch_multiplier_nontrivial_field p hp
  have hE := actual_balanced_branch_jets_field p hp
  change branchEval (actualBalancedField p hp)=branchEval f*b ∧
    branchEval (D (actualBalancedField p hp))=branchEval (D f)*b at hE
  have hT0 : branchEval (actualNativeUVZeroBranch p hp)=0 := by
    have hC (a : ZMod p) : branchEval (LaurentPolynomial.C a)=a := by
      simp only [branchEval,LaurentPolynomial.eval₂_C,RingHom.id_apply]
    rw [actualNativeUVZeroBranch,map_sub,hC,sub_self]
  have hT := actual_whole_proper_three_branch_jets p hp
  change 6*f^2*actualNativeUVZeroBranch p hp-3*f^2*descendedP p^2-
    3*G^2-6*f*G*descendedP p+6*G*delta+2*f*actualWholeProperParticular p hp-
      6*f*actualBalancedField p hp=f^2*R at hfactor
  have he := native_ratio_branch_value f G (descendedP p) delta
    (actualNativeUVZeroBranch p hp) (actualWholeProperParticular p hp)
    (actualBalancedField p hp) R b h2 hf (actual_native_G_three_branch_jets p hp)
    ⟨hT.1,hT.2.1⟩ hT0 hE hfactor
  rw [actual_P_branch_zero p hp,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,zero_sub] at he
  have hhalf : (2 : ZMod p)*(3/2 : ZMod p)=3 := by field_simp [h2]
  change branchEval R=12*q^2+9*q*r
  dsimp only [b] at he
  linear_combination he+3*q*r*hhalf

end WPFieldAssembly.SourceClosureBalancedNativeBranch
