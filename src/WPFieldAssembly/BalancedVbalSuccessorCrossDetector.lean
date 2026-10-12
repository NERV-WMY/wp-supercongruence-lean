import WPFieldAssembly.BalancedVbalSuccessorCrossEnds
import WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualGaussBottom WPFiniteWSource
  WPFieldAssembly.BalancedVbalSuccessorCrossSupport
  WPFieldAssembly.BalancedVbalSuccessorCrossEnds
  WPFieldAssembly.BalancedVbalSuccessorCrossTruncation
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.BalancedVbalSuccessorCrossDetector

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

/- STATEMENT_FIDELITY: the detector uses the SAME full actualNcross,
   retaining all four phases until the actual support projection. Its
   positive shift is evaluated using the genuine Laurent realization,
   and originPole uses every negative coefficient of invert(actualNcross).
   No caller carrier, endpoint, source or nonzero harmonic premise is
   introduced. This detector does not assert the coupled-source identity. -/

theorem actual_cross_native_half_powers (hp : 19≤p) :
    (1/4 : ZMod p)^((p-1)/2)=1 ∧ (4 : ZMod p)^((p-1)/2)=1 := by
  have hb : (4 : ZMod p)^((p-1)/2)=1 := four_half_power p hp
  refine ⟨?_,hb⟩
  rw [div_pow,one_pow,hb,div_one]

/-- The actual support realization keeps the positive shift equal to Dx at both units. -/
theorem actual_cross_shift_native_evaluations (hp : 19≤p) :
    (actualCrossShift p).eval (1/4)=
        LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp)
          (actualCrossDx p) ∧
      (actualCrossShift p).eval 4=
        LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp)
          (actualCrossDx p) := by
  have hreal := actual_cross_shift_realization p hp
  obtain ⟨hqa,hqb⟩ := actual_cross_unit_values p hp
  obtain ⟨hqaN,hqbN⟩ := actual_cross_native_half_powers p hp
  constructor
  · have h := congrArg
      (fun L : (ZMod p)[T;T⁻¹] =>
        LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossQuarterUnit p hp) L)
      hreal
    simpa only [LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,map_mul,
      LaurentPolynomial.eval₂_T,zpow_natCast,Units.val_pow_eq_pow_val,hqa,hqaN,one_mul]
      using h
  · have h := congrArg
      (fun L : (ZMod p)[T;T⁻¹] =>
        LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (actualCrossFourUnit p hp) L)
      hreal
    simpa only [LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,map_mul,
      LaurentPolynomial.eval₂_T,zpow_natCast,Units.val_pow_eq_pow_val,hqb,hqbN,one_mul]
      using h

theorem actual_cross_shift_native_ends (hp : 19≤p) :
    (actualCrossShift p).eval (1/4)= -15*fieldHarmonic p (p/6)^2 ∧
      (actualCrossShift p).eval 4=120*fieldHarmonic p (p/6)^2 := by
  obtain ⟨ha,hb⟩ := actual_cross_shift_native_evaluations p hp
  obtain ⟨hda,hdb⟩ := actual_cross_Dx_native_ends p hp
  exact ⟨ha.trans hda,hb.trans hdb⟩

/-- The actual four-phase projection evaluates with its original 93 and -44 coefficients. -/
theorem actual_Ncross_trunc_ends (hp : 19≤p) :
    (trunc (actualNcross p)).eval (1/4)=
        -(123/25 : ZMod p)*fieldHarmonic p (p/6)^2 ∧
      (trunc (actualNcross p)).eval 4=
        -(996/25 : ZMod p)*fieldHarmonic p (p/6)^2 := by
  obtain ⟨ha,hb⟩ := actual_cross_shift_native_ends p hp
  have hproj := actual_cross_four_phase_projection p hp
  have h4p : (4 : ZMod p)^p=4 := ZMod.pow_card 4
  have hqp : (1/4 : ZMod p)^p=1/4 := by rw [div_pow,one_pow,h4p]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h250 : (250 : ZMod p)≠0 := by
    rw [show (250 : ZMod p)=2*5^3 by ring]
    exact mul_ne_zero h2 (pow_ne_zero _ h5)
  constructor
  · rw [hproj]
    simp only [eval_mul,eval_C,eval_sub,eval_ofNat,eval_pow,eval_X,hqp,ha]
    field_simp [h4,h25,h250]; ring
  · rw [hproj]
    simp only [eval_mul,eval_C,eval_sub,eval_ofNat,eval_pow,eval_X,h4p,hb]
    field_simp [h25,h250]; ring

/-- The checked origin operator gives the literal detector on invert of the full Ncross. -/
theorem actual_Ncross_origin_inverse_detector (hp : 19≤p) :
    originPole (invert (actualNcross p))=
      (291/125 : ZMod p)*fieldHarmonic p (p/6)^2 := by
  obtain ⟨ha,hb⟩ := actual_Ncross_trunc_ends p hp
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h15 : (15 : ZMod p)≠0 := by
    rw [show (15 : ZMod p)=3*5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : ZMod p)≠0 := by
    rw [show (25 : ZMod p)=5^2 by ring]
    exact pow_ne_zero _ h5
  have h125 : (125 : ZMod p)≠0 := by
    rw [show (125 : ZMod p)=5^3 by ring]
    exact pow_ne_zero _ h5
  rw [originPole_trunc_inverse,LaurentPolynomial.involutive_invert,ha,hb]
  field_simp [h15,h25,h125]; ring

/-- The original 2/9 normalization is computed from the actual detector. -/
theorem actual_Ncross_origin_inverse_normalized (hp : 19≤p) :
    (2/9 : ZMod p)*originPole (invert (actualNcross p))=
      (194/375 : ZMod p)*fieldHarmonic p (p/6)^2 := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h9 : (9 : ZMod p)≠0 := by
    rw [show (9 : ZMod p)=3^2 by ring]
    exact pow_ne_zero _ h3
  have h125 : (125 : ZMod p)≠0 := by
    rw [show (125 : ZMod p)=5^3 by ring]
    exact pow_ne_zero _ h5
  have h375 : (375 : ZMod p)≠0 := by
    rw [show (375 : ZMod p)=3*5^3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero _ h5)
  rw [actual_Ncross_origin_inverse_detector p hp]
  field_simp [h9,h125,h375]; ring

end WPFieldAssembly.BalancedVbalSuccessorCrossDetector
