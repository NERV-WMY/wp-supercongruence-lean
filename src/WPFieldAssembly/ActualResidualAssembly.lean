import WPFieldAssembly.ActualNextHermite
import WPFieldAssembly.ActualLowEuler
import WPFieldAssembly.ActualBalancedNodeAttachment

open scoped Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction WPActualChiSource WPActualGaussBottom WPFiniteCarry
  WPActualRankTwoLegendreField WPActualRankTwoComparison
  WPActualRankTwoProper WPActualRankTwoLowTaylor
  WPActualRankTwoResidueSource WPActualRankTwoCarryField
  WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualNC77Chart
  WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.ResidualProjection
  WPFieldAssembly.ActualDeltaUNextSource
  WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualNextHermite
  WPFieldAssembly.ActualLowEuler
  WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.ActualR0Node
  WPFieldAssembly.NativeIR28
  WPFieldAssembly.NativeFullGreen
  WPFieldAssembly.NativeScalarRows
  WPFiniteLaurentDifferential
  WPMomentPrecision.NativeSecondLift

namespace WPFieldAssembly.ActualResidualAssembly

set_option maxHeartbeats 1800000

theorem hermiteOperator_top {K : Type*} [Field K]
    (Y P : K[X]) (d e : ℕ)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (hY : Y.natDegree ≤ d) (hP : P.natDegree ≤ e) :
    (hermiteOperator Y P).coeff (d + e + 1) =
      -((e : K) - 2 * (d : K)) * Y.coeff d * P.coeff e := by
  let q : K[X] := 1 - X ^ 2
  have hDY : Y.derivative.natDegree ≤ d - 1 := by
    have h := natDegree_derivative_le Y
    omega
  have hprod : (Y.derivative * P).natDegree ≤ d - 1 + e :=
    natDegree_mul_le_of_le hDY hP
  have hpc :
      (Y.derivative * P).coeff (d - 1 + e) =
        (d : K) * Y.coeff d * P.coeff e := by
    rw [coeff_mul_add_eq_of_natDegree_le hDY hP,
      coeff_derivative, show d - 1 + 1 = d by omega]
    have hc : ((d - 1 : ℕ) : K) + 1 = (d : K) := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hd]
    linear_combination Y.coeff d * P.coeff e * hc
  have hq : q.natDegree ≤ 2 := by
    have hx : (X ^ 2 : K[X]).natDegree ≤ 2 := by
      simp only [natDegree_X_pow]
      exact le_rfl
    dsimp only [q]
    exact (natDegree_sub_le_of_le
      (show (1 : K[X]).natDegree ≤ 0 by simp) hx).trans (by omega)
  have hqc : q.coeff 2 = (-1 : K) := by
    dsimp only [q]
    simp only [coeff_sub, coeff_one, coeff_X_pow, show (2 : ℕ) ≠ 0 by omega,
      if_false, if_true, zero_sub]
  have hqp :
      (q * (Y.derivative * P)).coeff (d + e + 1) =
        -(d : K) * Y.coeff d * P.coeff e := by
    rw [show d + e + 1 = 2 + (d - 1 + e) by omega,
      coeff_mul_add_eq_of_natDegree_le hq hprod, hqc, hpc]
    ring
  have hsplit :
      hermiteOperator Y P =
        q * (Y * P.derivative - Y.derivative * P) -
          q * (Y.derivative * P) := by
    dsimp only [hermiteOperator, q]
    ring
  have hw := quadraticWronskian_top Y P d e hd he hY hP
  change
    (q * (Y * P.derivative - Y.derivative * P)).coeff
      (d + e + 1) =
      -((e : K) - (d : K)) * Y.coeff d * P.coeff e at hw
  rw [hsplit, coeff_sub, hw, hqp]
  ring

variable (p : ℕ) [Fact p.Prime]

theorem actual_hermite_degree_drop (hp : 19 ≤ p)
    (P S : (ZMod p)[X])
    (hP : P.natDegree < p)
    (hS : S.natDegree ≤ 3 * (p / 6) - 1)
    (hsource : hermiteOperator (actualLegendreJacobi p) P = S) :
    P.natDegree ≤ 2 * (p / 6) := by
  by_contra hh
  let d := p / 6
  let e := P.natDegree
  let Y := actualLegendreJacobi p
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have he : 2 * d < e := by dsimp only [d, e]; omega
  have hydeg : Y.natDegree = d := actual_legendre_exact_degree p hp
  have hyne : Y ≠ 0 := by
    intro hz
    simp only [hz, natDegree_zero] at hydeg
    omega
  have hpne : P ≠ 0 := by
    intro hz
    have hzdeg : e = 0 := by simp [e, hz]
    omega
  have hyc : Y.coeff d ≠ 0 := by
    rw [← hydeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hyne
  have hpc : P.coeff e ≠ 0 := by
    dsimp only [e]
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hpne
  have hcast :
      ((e - 2 * d : ℕ) : ZMod p) =
        (e : ZMod p) - 2 * (d : ZMod p) := by
    rw [Nat.cast_sub (by omega : 2 * d ≤ e)]
    push_cast
    ring
  have hu : (e : ZMod p) - 2 * (d : ZMod p) ≠ 0 := by
    rw [← hcast]
    exact WPActualGaussProper.small_cast_ne_zero p
      (e - 2 * d) (by omega) (by dsimp only [e] at *; omega)
  have hc := congrArg
    (fun Q : (ZMod p)[X] => Q.coeff (d + e + 1)) hsource
  change
    (hermiteOperator Y P).coeff (d + e + 1) =
      S.coeff (d + e + 1) at hc
  rw [hermiteOperator_top Y P d e (by omega) (by omega)
    (le_of_eq hydeg) (by dsimp only [e]; exact le_rfl)] at hc
  have hs : S.coeff (d + e + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hS.trans_lt (by dsimp only [d] at *; omega))
  rw [hs] at hc
  exact (mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hu) hyc) hpc) hc

noncomputable def actualProperMetric : (ZMod p)[X] :=
  actualLegendreJacobi p ^ 2 * actualM p -
    actualLegendreJacobi p * properLegendreJacobi p *
      adjacentPrimitive p (p / 6)

theorem actual_proper_metric_source (hp : 19 ≤ p) :
    hermiteOperator (actualLegendreJacobi p) (actualProperMetric p) =
      actualLegendreJacobi p *
        (actualLegendreJacobi p * properLegendreJacobi p -
          adjacentPrimitive p (p / 6)) := by
  have hm := (actual_M_source_degree p hp).1
  simp only [actualMNumerator] at hm
  have hw := properLegendreJacobi_wronskian p (by omega : 7 ≤ p)
  have hb := (actual_adjacent_primitive_data p hp).1
  simp only [actualProperMetric, hermiteOperator, derivative_sub,
    derivative_mul, derivative_pow_succ, Nat.cast_one, one_add_one_eq_two, C_ofNat]
  linear_combination
    actualLegendreJacobi p ^ 3 * hm -
      actualLegendreJacobi p * adjacentPrimitive p (p / 6) * hw -
      actualLegendreJacobi p ^ 2 * properLegendreJacobi p * hb

theorem actual_proper_metric_degree (hp : 19 ≤ p) :
    (actualProperMetric p).natDegree ≤ 2 * (p / 6) := by
  let d := p / 6
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let B := adjacentPrimitive p d
  have hd : 3 ≤ d := by dsimp only [d]; omega
  have hy : Y.natDegree ≤ d := actualLegendreJacobi_degree p
  have hn : n.natDegree ≤ d - 1 := by
    have h := properLegendreJacobi_degree p (by omega : 7 ≤ p)
    dsimp only [n, d] at *
    omega
  have hb : B.natDegree ≤ 2 * d - 1 := adjacentPrimitive_degree p d
  have hf : (Y ^ 2).natDegree ≤ 2 * d := by
    simpa [Nat.mul_comm] using natDegree_pow_le_of_le 2 hy
  have hfm : (Y ^ 2 * actualM p).natDegree ≤ 4 * d - 2 :=
    (natDegree_mul_le_of_le hf
      (actual_M_source_degree p hp).2.1).trans
        (by dsimp only [d] at *; omega)
  have hyn : (Y * n).natDegree ≤ 2 * d - 1 :=
    (natDegree_mul_le_of_le hy hn).trans (by omega)
  have hynb : (Y * n * B).natDegree ≤ 4 * d - 2 :=
    (natDegree_mul_le_of_le hyn hb).trans (by omega)
  have hinit : (actualProperMetric p).natDegree ≤ 4 * d - 2 := by
    change (Y ^ 2 * actualM p - Y * n * B).natDegree ≤ _
    simpa only [max_self] using natDegree_sub_le_of_le hfm hynb
  have hmid : (Y * n - B).natDegree ≤ 2 * d - 1 := by
    simpa only [max_self] using natDegree_sub_le_of_le hyn hb
  have hrhs : (Y * (Y * n - B)).natDegree ≤ 3 * d - 1 :=
    (natDegree_mul_le_of_le hy hmid).trans (by omega)
  apply actual_hermite_degree_drop p hp
      (actualProperMetric p) (Y * (Y * n - B))
  · exact hinit.trans_lt (by dsimp only [d]; omega)
  · exact hrhs
  · exact actual_proper_metric_source p hp

theorem actual_proper_metric_projection_zero (hp : 19 ≤ p) (j : ℕ) :
    Ij p j (quadraticInverse (actualProperMetric p)) = 0 :=
  low_correction_both_projections_zero p hp _
    (quadraticInverse_degree_of_le _ (p / 6)
      (actual_proper_metric_degree p hp)) j

theorem actual_proper_metric_QO (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p ^ 2 * actualM p) =
      QO p (actualLegendreJacobi p * properLegendreJacobi p *
        adjacentPrimitive p (p / 6)) := by
  have hz := actual_proper_metric_projection_zero p hp 0
  change QO p (actualProperMetric p) = 0 at hz
  rw [actualProperMetric, QO_sub_local] at hz
  exact sub_eq_zero.mp hz

theorem actual_PSrc_source_six (hp : 19 ≤ p) :
    C (6 : ZMod p) * actualPSrc p hp +
        actualVariationField p (by omega) *
          actualRankDividedField p (by omega) =
      C (6 * actualLowConstant p) *
          (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) -
        C (2 : ZMod p) * (X ^ p * actualC p hp) +
        C (6 : ZMod p) *
          (actualLegendreJacobi p ^ 2 *
            (actualM p +
              WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6)))) -
        C (6 : ZMod p) *
          (actualLegendreJacobi p * properLegendreJacobi p *
            (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p)) := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let R := actualRankDividedField p (by omega : 7 ≤ p)
  let B := adjacentPrimitive p (p / 6)
  let O : (ZMod p)[X] := WPFiniteKSource.OP p
  let L : (ZMod p)[X] := WPFiniteKSource.LPsrc p
  let Kc := WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))
  let c := actualLowConstant p
  let h := fieldHarmonic p (p / 6)
  let u : (ZMod p)[X] := X ^ p
  have hr : R = Y * (L - C h) - u * n := by
    dsimp only [R]
    rw [WPActualRankTwoComparison.actual_rankDividedField_eq_hat p hp]
    dsimp only [rankHatField, Y, L, h, u, n,
      WPFiniteKSource.LPsrc, WPFiniteKSource.EP, WPFiniteNC122.q,
      evenLogPolynomial]
    simp only [map_sub]
    ring
  have hpoly :
      Y * actualSixS p hp + R * A =
        6 * Y * n * (C c * u - B - O) -
          2 * u * actualC p hp +
          6 * Y ^ 2 * (actualM p + Kc) := by
    dsimp only [actualSixS]
    linear_combination
      -u * (actual_C_division_degree p hp).1 + A * hr
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have hu : C (6 : ZMod p) * C (1 / 6 : ZMod p) =
      (1 : (ZMod p)[X]) := by
    rw [← C_mul]
    simp [h6]
  have hclear :
      C (6 : ZMod p) * actualPSrc p hp = Y * actualSixS p hp := by
    dsimp only [actualPSrc]
    rw [← mul_assoc, hu, one_mul]
  calc
    _ = Y * actualSixS p hp + R * A := by rw [hclear]; ring
    _ = 6 * Y * n * (C c * u - B - O) -
          2 * u * actualC p hp +
          6 * Y ^ 2 * (actualM p + Kc) := hpoly
    _ = _ := by
      simp only [map_mul, map_ofNat]
      ring

theorem actual_PSrc_QO_source (hp : 19 ≤ p) :
    6 * QO p (actualPSrc p hp) +
        QO p (actualVariationField p (by omega) *
          actualRankDividedField p (by omega)) =
      6 * actualLowConstant p *
          QO p (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) -
        2 * QO p (X ^ p * actualC p hp) +
        6 * QO p (actualLegendreJacobi p ^ 2 *
          (actualM p +
            WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6)))) -
        6 * QO p (actualLegendreJacobi p * properLegendreJacobi p *
          (adjacentPrimitive p (p / 6) + WPFiniteKSource.OP p)) := by
  have h := congrArg (QO p) (actual_PSrc_source_six p hp)
  simpa only [QO_add, QO_sub_local, QO_C_mul] using h

theorem actual_original_norm_full (hp : 19 ≤ p) :
    (originalNorm p : ZMod p) =
      QO p (actualRankDividedField p (by omega) ^ 2) / 3 +
        (5 / 24 : ZMod p) *
          Ij p 1 (quadraticInverse
            (actualRankDividedField p (by omega) ^ 2)) := by
  let R := actualRankDividedField p (by omega : 7 ≤ p)
  have hs : (C (1 / 6 : ZMod p) * R) ^ 2 =
      C ((1 / 6 : ZMod p) ^ 2) * R ^ 2 := by
    simp only [map_pow]
    ring
  dsimp only [R] at hs
  rw [original_norm_actual_source p hp]
  simp only [hs, quadraticInverse_C_mul, Ij_C_mul]
  unfold QO
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  field_simp [h2, h3, h6, h24]
  ring

noncomputable def actualResidualPolynomial (hp : 19 ≤ p) : (ZMod p)[X] :=
  C (-2 * actualLowConstant p) *
      (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) -
    C (2 : ZMod p) *
      (actualLegendreJacobi p ^ 2 *
        WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) +
    C (2 : ZMod p) *
      (actualLegendreJacobi p * properLegendreJacobi p *
        WPFiniteKSource.OP p) -
    actualRankDividedField p (by omega) ^ 2

noncomputable def actualLowPair : ZMod p :=
  (substituteOver (ActualLowEuler.actualH p)
      (NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) *
    D (substituteOver (actualSecondLogField p)
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent)).coeff (-1)

theorem actual_residual_polynomial_QO (hp : 19 ≤ p) :
    QO p (actualResidualPolynomial p hp) =
      -2 * actualLowConstant p *
          QO p (X ^ p * actualLegendreJacobi p * properLegendreJacobi p) -
        2 * QO p (actualLegendreJacobi p ^ 2 *
          WPFiniteKSource.KsrcP p (fieldHarmonic p (p / 6))) +
        2 * QO p (actualLegendreJacobi p * properLegendreJacobi p *
          WPFiniteKSource.OP p) -
        QO p (actualRankDividedField p (by omega) ^ 2) := by
  simp only [actualResidualPolynomial, QO_add, QO_sub_local, QO_C_mul]

theorem actual_residual_balanced_source (hp : 19 ≤ p) :
    2 * residueHom p (integralDeltaUDigit p hp) -
        (originalNorm p : ZMod p) - nativeBpair p hp =
      2 * residueHom p (balancedGreenDigitIntegral p hp) +
        (2 / 3 : ZMod p) * actualLowPair p +
        2 * (actualSecondLogField p).eval (4 / 125) +
        QO p (actualResidualPolynomial p hp) / 3 -
        (5 / 24 : ZMod p) *
          Ij p 1 (quadraticInverse
            (actualRankDividedField p (by omega) ^ 2)) -
        nativeBpair p hp := by
  have hd := actual_deltaU_digit_low_next_source p hp
  have hb := actual_SB71d p hp
  have he := actual_second_log_QO_NC87 p hp
  change
    QO p (actualLegendreJacobi p ^ 2 *
      (actualSecondLogField p).comp (1 - X ^ 2)) =
      actualLowPair p +
        3 * (actualSecondLogField p).eval (4 / 125) at he
  have hq := actual_PSrc_QO_source p hp
  simp only [mul_add, QO_add] at hq
  have hn := actual_original_norm_full p hp
  have hs := actual_residual_polynomial_QO p hp
  have hm := actual_proper_metric_QO p hp
  unfold actualTangentGroup at hb
  simp only [QO_add] at hb
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 9 (by omega) (by omega)
  have h18 : (18 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 18 (by omega) (by omega)
  have h24 : (24 : ZMod p) ≠ 0 := by
    rw [show (24 : ZMod p) = 2 ^ 3 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h3
  linear_combination
    (norm := (field_simp [h2, h3, h6, h9, h18, h24]; ring))
      2 * hd + 2 * hb + (2 / 3 : ZMod p) * he -
        (1 / 9 : ZMod p) * hq - hn -
        (1 / 3 : ZMod p) * hs - (2 / 3 : ZMod p) * hm

end WPFieldAssembly.ActualResidualAssembly
