import WPMomentPrecision.SecondLift.OriginalCentralDigit
import WPMomentPrecision.CanonicalPairReduction

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoParameter
  WPActualRankTwoLowTaylor WPActualRankTwoLegendreField WPActualNativeJacobiJet WPActualNativeCanonicalPart
  WPActualPositivePair WPActualTerminatingSquare
  WPMomentPrecision.NativeSecondLift WPMomentPrecision.NativeQSource
  WPMomentPrecision.RationalEulerPrimitive

namespace WPMomentPrecision.HJetYUAttachment

set_option maxHeartbeats 1800000

theorem integralEuler_field (p e : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (he : e < p)
    (P : (integralRationals p)[X])
    (hdegree : (P.map (integralRationals p).subtype).natDegree ≤ e) :
    (integralEuler p e hp he P).map (residueHom p) = eulerPrimitive p (P.map (residueHom p)) := by
  ext n
  rw [coeff_map, eulerPrimitive_coeff]
  have hv := congrArg (fun Q : ℚ[X] => Q.coeff n) (integralEuler_value p e hp he P)
  rw [coeff_map] at hv
  change ((integralEuler p e hp he P).coeff n).val =
    (rationalEuler e (P.map (integralRationals p).subtype)).coeff n at hv
  change (((integralEuler p e hp he P).coeff n).val : ZMod p) = _
  rw [hv, rationalEuler_coeff]
  by_cases hn : n < e + 1
  · rw [if_pos hn]
    by_cases hz : n = 0
    · subst n
      simp only [Nat.cast_zero, div_zero, Rat.cast_zero]
    · have hu : (n : ZMod p) ≠ 0 :=
        WPActualGaussProper.small_cast_ne_zero p n (by omega) (by omega)
      have hnum : (((n : ℚ).num : ℤ) : ZMod p) ≠ 0 := by simpa using hu
      have hi : (P.map (integralRationals p).subtype).coeff n ∈ integralRationals p := by
        rw [coeff_map]
        exact (P.coeff n).property
      rw [Rat.cast_div_of_ne_zero (integral_denominator_cast_ne_zero p _ hi) hnum,
        Rat.cast_natCast, coeff_map]
      rw [coeff_map]
      change ((P.coeff n).val : ZMod p) / (n : ZMod p) =
        ((P.coeff n).val : ZMod p) / (n : ZMod p)
      rfl
  · rw [if_neg hn, Rat.cast_zero]
    have hzero := coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (by omega : e < n))
    have hres : (P.map (residueHom p)).coeff n = 0 := by
      rw [coeff_map] at hzero ⊢
      change (P.coeff n).val = 0 at hzero
      change (((P.coeff n).val : ℚ) : ZMod p) = 0
      rw [hzero, Rat.cast_zero]
    rw [hres, zero_div]

/-- The actual rational YU coefficient polynomial reduces to J/12 because
the full first-jet attachment is transported through the injective q chart. -/
theorem actual_YU_q_first_jet (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    C (12 : ZMod p) * (integralActualYUQ p hp).map (residueHom p) =
      WPActualNativeJetODE.nativeJetField p := by
  have hi : (integralActualYUQ p hp).comp (1 - X ^ 2) =
      rankIntegralJacobi p (by omega) 1 * integralU p (by omega) := by
    apply polynomial_subtype_injective p
    change ((integralActualYUQ p hp).comp (1 - X ^ 2)).map (integralRationals p).subtype =
      (rankIntegralJacobi p (by omega) 1 * integralU p (by omega)).map (integralRationals p).subtype
    rw [Polynomial.map_comp, integralActualYUQ_value, Polynomial.map_mul,
      rankIntegralJacobi_value, integralU_value]
    simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
    exact actual_YU_q_source p hp
  have hf := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p)) hi
  simp only [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
    rankIntegralJacobi_field] at hf
  apply quadratic_comp_injective
  change (C (12 : ZMod p) * (integralActualYUQ p hp).map (residueHom p)).comp
      (1 - X ^ 2) = (WPActualNativeJetODE.nativeJetField p).comp (1 - X ^ 2)
  rw [mul_comp, C_comp, hf]
  rw [← mul_assoc]
  rw [Polynomial.C_ofNat 12]
  change 12 * WPActualRankTwoLegendreField.actualLegendreJacobi p *
      actualUField p (by omega) = nativeJacobiJet p
  exact (actual_native_jet_twelve_YU p hp).symm

/-- The primitive uses the original full coefficient cutoff. Its source is
the literal H_J, so the common endpoint is fixed rather than assigned. -/
theorem actual_HJet_YU_polynomial (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeHJet p = C (12 : ZMod p) *
      (integralEuler p (p - 1 - p / 6) hp (by omega) (integralActualYUQ p hp)).map (residueHom p) := by
  have hdegree : ((integralActualYUQ p hp).map (integralRationals p).subtype).natDegree ≤
      p - 1 - p / 6 := by
    rw [integralActualYUQ_value]
    have hd := Nat.div_mul_le_self p 6
    exact (actual_YU_q_degree p hp).trans (by omega)
  rw [integralEuler_field p _ hp (by omega) _ hdegree, nativeHJet,
    ← actual_YU_q_first_jet p hp]
  ext n
  rw [eulerPrimitive_coeff, coeff_C_mul, coeff_C_mul, eulerPrimitive_coeff]
  ring

theorem actual_HJet_YU_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPMomentPrecision.ResonancePair.C0 p = 12 *
      (((rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) := by
  let H := integralEuler p (p - 1 - p / 6) hp (by omega) (integralActualYUQ p hp)
  have hx : residueHom p (integralCMPoint p hp) = (4 / 125 : ZMod p) := by
    change (((integralCMPoint p hp).val : ℚ) : ZMod p) = _
    rw [integralCMPoint_value]
    norm_num [Rat.cast_def]
  have he : (H.map (residueHom p)).eval (4 / 125 : ZMod p) =
      (((rationalEuler (p - 1 - p / 6) (actualYUQ p)).eval (4 / 125 : ℚ) : ℚ) : ZMod p) := by
    rw [← hx, eval_map_apply]
    change (((integralEulerValue p (p - 1 - p / 6) hp (by omega)
      (integralActualYUQ p hp)).val : ℚ) : ZMod p) = _
    rw [integralEulerValue_value, integralActualYUQ_value]
  rw [WPMomentPrecision.ResonancePair.C0_original_endpoint,
    actual_HJet_YU_polynomial p hp, eval_mul, eval_C, he]

/- The original negative digit chain above is complete source, subject to the
root's pending compiler/FIVE check, and it retains the actual full F cutoff.
The separate NC75 attachment has the following precise next obligation.
Construct the ordinary second derivative of the actual rank-two quotient
family through its full p-1 cutoff, attach its reduction y2, and prove the
finite Clausen jet vanishing for
  E2 = K(q) - 2 R^2 - 2 Y y2
through every z_T coefficient below p. Only then may one define the actual
P2 from E2 = z_T^p P2 and transport its nonzero logarithmic residue b_P2 with
the cubic factor 1/3 and the signed conic Jacobian. No theorem here replaces
that full rank-two cutoff by e, assigns P2 from an endpoint, or removes b_P2.
The IR29 derivation instead extracts the same whole actual F directly from
the integral q expansion and proves the low L2 contribution divisible by p.
Its remaining scalar contraction is owned by the root's NC77 integration. -/

end WPMomentPrecision.HJetYUAttachment
