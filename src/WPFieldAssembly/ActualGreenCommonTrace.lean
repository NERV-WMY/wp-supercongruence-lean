import WPFieldAssembly.ActualGreenTrace
import WPFieldAssembly.ActualBalancedTrace
import WPFieldAssembly.LaurentPoleTrace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualBalancedGreenTransfer WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen WPFieldAssembly.NativeOriginalResidues

namespace WPFieldAssembly.ActualGreenCommonTrace

set_option maxHeartbeats 1600000

noncomputable def lowFpullQ (p : ℕ) : ℚ[T;T⁻¹] :=
  ((squareQ p).comp WPActualPullbackSource.Vpolynomial).toLaurent

noncomputable def lowReflectionDefectQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
    (actualReflectionDefectIntegral p hp)

theorem pole_Abar_eq : LaurentPoleTrace.Abar = (WPFiniteZSource.Abar : ℚ[X]) := by
  unfold LaurentPoleTrace.Abar WPFiniteZSource.Abar
  ring

theorem trace_one_eq_inverseAtrace (L : ℚ[T;T⁻¹]) :
    LaurentPoleTrace.trace 1 L = inverseAtrace L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add, hL, hM]
  | C_mul_T n a =>
    rw [LaurentPoleTrace.trace_monomial, inverseAtrace_monomial]
    cases n with
    | ofNat n =>
      simpa only [Int.ofNat_eq_natCast, inverseAweight] using
        congrArg (fun q : ℚ => a * q) (LaurentPoleTrace.weight_one_nat n)
    | negSucc n =>
      rw [LaurentPoleTrace.weight_support 1 _ (by omega)]
      rfl

/-- The literal rational K_w dlog Q, with its full denominator Abar^(p+1). -/
noncomputable def weightedDlogQtrace (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (LaurentPoleTrace.trace (p + 1)).comp
    ({
      toFun := fun L => LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
        T ((p - 1 : ℕ) : ℤ) * (4 * T 1 - 11) ^ p * (4 - 11 * T 1) * L
      map_add' := by intro L M; ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem weightedDlogQtrace_apply (p : ℕ) (L : ℚ[T;T⁻¹]) :
    weightedDlogQtrace p L = LaurentPoleTrace.trace (p + 1)
      (LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
        T ((p - 1 : ℕ) : ℤ) * (4 * T 1 - 11) ^ p * (4 - 11 * T 1) * L) := rfl

private theorem dlogQtrace_apply (L : ℚ[T;T⁻¹]) :
    dlogQtrace L = inverseAtrace (3 * T (-1) * (4 - 11 * T 1) * L) := rfl

noncomputable def zetaQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1 / 3 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) *
    T (-(p : ℤ)) * (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p

theorem actual_zeta_rational_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype
      (actualZetaIntegral p) = zetaQ p := by
  simp only [actualZetaIntegral, zetaQ, map_mul, map_pow,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_toLaurent, Subring.subtype_apply, Nat.cast_ofNat,
    WPActualRankTwoHatLift.smallIntegralInverse_value p 3 (by omega) (by omega),
    WPActualRankTwoHatLift.smallIntegralInverse_value p 5 (by omega) (by omega),
    actualAbarIntegral, WPFiniteZSource.Abar, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]

theorem weighted_zeta_scalar (p : ℕ) :
    (9 * (5 : ℚ) ^ (p - 1)) *
      ((1 / 3 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) =
      3 * (1 / 5 : ℚ) ^ (p - 1) := by
  have h : (5 : ℚ) ^ (p - 1) * (1 / 5 : ℚ) ^ (p - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [Nat.mul_comm 2 (p - 1), pow_mul]
  linear_combination 3 * (1 / 5 : ℚ) ^ (p - 1) * h

/-- Exact cancellation of the actual K_w and zeta weights, including 5^(p-1). -/
theorem actual_weighted_zeta_trace (p : ℕ) (hp : 0 < p) (L : ℚ[T;T⁻¹]) :
    weightedDlogQtrace p (zetaQ p * L) =
      (1 / 5 : ℚ) ^ (p - 1) * dlogQtrace ((4 * T 1 - 11) ^ p * L) := by
  let k : ℚ := (1 / 5) ^ (p - 1)
  let B : ℚ[T;T⁻¹] := 3 * T (-1) * (4 - 11 * T 1) * (4 * T 1 - 11) ^ p * L
  have ht : (T ((p - 1 : ℕ) : ℤ) : ℚ[T;T⁻¹]) * T (-(p : ℤ)) = T (-1) := by
    rw [← T_add]
    congr 1
    omega
  have hc : LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
      LaurentPolynomial.C ((1 / 3 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) =
      LaurentPolynomial.C (3 * k) := by
    rw [← map_mul, weighted_zeta_scalar]
  have he : LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
      T ((p - 1 : ℕ) : ℤ) * (4 * T 1 - 11) ^ p * (4 - 11 * T 1) * (zetaQ p * L) =
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p * (LaurentPolynomial.C k * B) := by
    unfold zetaQ
    calc
      _ = (LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
          LaurentPolynomial.C ((1 / 3 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1)))) *
          (T ((p - 1 : ℕ) : ℤ) * T (-(p : ℤ))) *
          (4 * T 1 - 11) ^ p * (4 - 11 * T 1) *
          (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ p * L := by ring
      _ = _ := by rw [hc, ht]; simp only [map_mul, map_ofNat, B]; ring
  rw [weightedDlogQtrace_apply, he, ← pole_Abar_eq, Nat.add_comm p 1,
    LaurentPoleTrace.trace_cleared_pow, trace_one_eq_inverseAtrace, inverseAtrace_C_mul]
  change k * inverseAtrace B = k * dlogQtrace ((4 * T 1 - 11) ^ p * L)
  rw [dlogQtrace_apply]
  exact congrArg (fun F : ℚ[T;T⁻¹] => k * inverseAtrace F)
    (by dsimp only [B]; ring)

noncomputable def xiTraceQ (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (weightedDlogQtrace p).comp
    ({
      toFun := fun L => T (-(((p - 1) / 2 : ℕ) : ℤ)) * L
      map_add' := by intro L M; ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem xiTraceQ_apply (p : ℕ) (L : ℚ[T;T⁻¹]) :
    xiTraceQ p L = weightedDlogQtrace p (T (-(((p - 1) / 2 : ℕ) : ℤ)) * L) := rfl

theorem xiTraceQ_C_mul (p : ℕ) (a : ℚ) (L : ℚ[T;T⁻¹]) :
    xiTraceQ p (LaurentPolynomial.C a * L) = a * xiTraceQ p L := by
  simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using (xiTraceQ p).map_smul a L

theorem actual_xi_zeta_trace (p : ℕ) (hp : 0 < p) (L : ℚ[T;T⁻¹]) :
    xiTraceQ p (zetaQ p * L) =
      (1 / 5 : ℚ) ^ (p - 1) * dlogQtrace
        (T (-(((p - 1) / 2 : ℕ) : ℤ)) * (4 * T 1 - 11) ^ p * L) := by
  rw [xiTraceQ_apply,
    show T (-(((p - 1) / 2 : ℕ) : ℤ)) * (zetaQ p * L) =
    zetaQ p * (T (-(((p - 1) / 2 : ℕ) : ℤ)) * L) by ring,
    actual_weighted_zeta_trace p hp]
  congr 2
  ring

theorem actual_CB_rational_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualCBIntegral p hp).map (WPPIntegralReduction.integralRationals p).subtype =
      ActualGreenPrimitive.greenCBq p hp := by
  simp only [actualCBIntegral, ActualGreenPrimitive.greenCBq,
    ActualGreenPrimitive.greenBq, comparisonCoordinateI,
    ActualGreenPrimitive.greenCoordinateQ, ActualGreenPrimitive.cubicTIntegral,
    WPFiniteCubicLog.Tc, Polynomial.map_comp,
    Polynomial.map_contract (by norm_num : (2 : ℕ) ≠ 0),
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_one, Polynomial.map_ofNat,
    Subring.subtype_apply, Nat.cast_ofNat,
    WPActualRankTwoHatLift.smallIntegralInverse_value p 5 (by omega) (by omega)]

theorem actual_balanced_numerator_Q_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualBalancedNumeratorQ p hp =
      zetaQ p * ((ActualGreenPrimitive.greenCBq p hp).toLaurent +
        T (((p - 1) / 2 : ℕ) : ℤ) * invert (ActualGreenPrimitive.greenCBq p hp).toLaurent) +
      T (((p - 1) / 2 : ℕ) : ℤ) * invert (lowFpullQ p) * comparisonRational p hp := by
  simp only [actualBalancedNumeratorQ, actualBalancedNumeratorIntegral,
    map_add, map_mul, actual_zeta_rational_value p hp,
    WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert,
    WPActualChiSource.coefficientMap_toLaurent, actual_CB_rational_value p hp,
    actualLowMIntegral, actualLowFIntegral, Polynomial.map_comp,
    squareQIntegral_value p hp, WPHasseIntegralTransport.integralV_map_rational,
    lowFpullQ, comparisonRational]

theorem actual_balanced_whole_p_source_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.C (p : ℚ) * actualBalancedDividedQ p hp =
      actualBalancedNumeratorQ p hp := by
  rw [actualBalancedDividedQ]
  have hu : LaurentPolynomial.C (p : ℚ) * LaurentPolynomial.C (1 / (p : ℚ)) =
      (1 : ℚ[T;T⁻¹]) := by
    rw [← map_mul,
      show (p : ℚ) * (1 / (p : ℚ)) = 1 by
        field_simp [show (p : ℚ) ≠ 0 by positivity], map_one]
  rw [← mul_assoc, hu, one_mul]

theorem actual_balanced_weighted_trace_source
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    xiTraceQ p (actualBalancedNumeratorQ p hp) =
      ActualDeltaUNextSource.QO p (X ^ p * ActualGreenPrimitive.greenBq p hp) +
      dlogQtrace (greenProperTraceNumeratorQ p hp) +
      weightedDlogQtrace p (invert (lowFpullQ p) * comparisonRational p hp) := by
  let N := (p - 1) / 2
  let CB := (ActualGreenPrimitive.greenCBq p hp).toLaurent
  let k : ℚ := (1 / 5) ^ (p - 1)
  have ht : (T (-(N : ℤ)) : ℚ[T;T⁻¹]) * T (N : ℤ) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hpos : xiTraceQ p (zetaQ p * CB) =
      ActualDeltaUNextSource.QO p (X ^ p * ActualGreenPrimitive.greenBq p hp) := by
    rw [actual_xi_zeta_trace p (by omega)]
    have he : k * dlogQtrace (T (-(N : ℤ)) * (4 * T 1 - 11) ^ p * CB) =
        dlogQtrace (T (-(N : ℤ)) * LaurentPolynomial.C k *
          (4 * T 1 - 11) ^ p * CB) := by
      rw [show T (-(N : ℤ)) * LaurentPolynomial.C k * (4 * T 1 - 11) ^ p * CB =
        LaurentPolynomial.C k * (T (-(N : ℤ)) * (4 * T 1 - 11) ^ p * CB) by ring,
        dlogQtrace_C_mul]
    exact he.trans (actual_positive_proper_trace p hp)
  have hneg : xiTraceQ p (zetaQ p * (T (N : ℤ) * invert CB)) =
      dlogQtrace (greenProperTraceNumeratorQ p hp) := by
    rw [actual_xi_zeta_trace p (by omega)]
    have he : T (-(N : ℤ)) * (4 * T 1 - 11) ^ p * (T (N : ℤ) * invert CB) =
        (4 * T 1 - 11) ^ p * invert CB := by
      linear_combination (4 * T 1 - 11) ^ p * invert CB * ht
    rw [he, greenProperTraceNumeratorQ,
      show LaurentPolynomial.C ((1 / 5 : ℚ) ^ (p - 1)) *
          (4 * T 1 - 11) ^ p * invert (ActualGreenPrimitive.greenCBq p hp).toLaurent =
        LaurentPolynomial.C ((1 / 5 : ℚ) ^ (p - 1)) *
          ((4 * T 1 - 11) ^ p * invert (ActualGreenPrimitive.greenCBq p hp).toLaurent)
        by ring,
      dlogQtrace_C_mul]
  have hperiod : xiTraceQ p (T (N : ℤ) * invert (lowFpullQ p) * comparisonRational p hp) =
      weightedDlogQtrace p (invert (lowFpullQ p) * comparisonRational p hp) := by
    rw [xiTraceQ_apply]
    change weightedDlogQtrace p
      (T (-(N : ℤ)) * (T (N : ℤ) * invert (lowFpullQ p) * comparisonRational p hp)) = _
    congr 1
    linear_combination invert (lowFpullQ p) * comparisonRational p hp * ht
  rw [actual_balanced_numerator_Q_source p hp, mul_add, map_add, map_add,
    hpos, hneg, hperiod]

noncomputable def balancedBraceQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ :=
  (ActualBalancedNodeAttachment.metricStar p hp).val * ActualDeltaUNextSource.QO p
      (WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2 *
        ActualCauchyMoment.unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) -
    weightedDlogQtrace p (invert (lowFpullQ p) * comparisonRational p hp) -
    dlogQtrace (greenProperTraceNumeratorQ p hp) -
    (3 / 2 : ℚ) * ActualDeltaUNextSource.QH p
      (WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2) -
    3 * WPFirstResidue.LiteralNormalization.literalR0 p

/-- SB98b attaches the actual reflected numerator to the original Cauchy norm over Q. -/
theorem actual_SB98b_before_division (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    3 * ActualCauchyTbarAttachment.coupledCauchyNormNumerator p hp =
      balancedBraceQ p hp + (p : ℚ) * xiTraceQ p (actualBalancedDividedQ p hp) := by
  have hs := actual_balanced_weighted_trace_source p hp
  rw [greenBq_actual_value p hp, ActualCauchyMoment.actual_SB82c p hp] at hs
  have ht := congrArg (xiTraceQ p) (actual_balanced_whole_p_source_Q p hp)
  rw [xiTraceQ_C_mul] at ht
  rw [ht, hs]
  unfold balancedBraceQ ActualCauchyTbarAttachment.coupledCauchyNormNumerator
  ring

theorem actual_low_square_pullback_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (squareQ p).comp (1 - X ^ 2) =
      WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2 := by
  let Y := WPActualRankTwoParameter.rankJacobiNode p 1
  let s : ℚ := (-1) ^ (p / 6)
  have hr := congrArg
    (fun P : (WPPIntegralReduction.integralRationals p)[X] =>
      P.map (WPPIntegralReduction.integralRationals p).subtype)
    (ActualGreenPrimitive.greenBalancedFirst_reflect p hp)
  have hy : Y.comp (-X) = Polynomial.C s * Y := by
    simpa only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_one, map_pow, map_neg, map_one,
      ActualBalancedNodeAttachment.balancedFirstIntegral_value p hp, Y, s] using hr
  have hs : s ^ 2 = 1 := by
    dsimp only [s]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hev : (Y ^ 2).comp (-X) = Y ^ 2 := by
    rw [pow_comp, hy, mul_pow, ← C_pow, hs, C_1, one_mul]
  exact ActualGreenPrimitive.quadraticInverse_even_pullback (Y ^ 2)
    (by norm_num : (2 : ℚ) ≠ 0) hev

theorem actual_low_square_origin_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (squareQ p).coeff 0 = 1 := by
  have h := congrArg (fun P : ℚ[X] => P.eval 1) (actual_low_square_pullback_Q p hp)
  simpa only [squareQ, eval_comp, eval_sub, eval_one, eval_pow,
    eval_X, one_pow, sub_self, WPActualRankTwoParameter.rankJacobiNode_endpoint_one,
    coeff_zero_eq_eval_zero] using h

theorem actual_low_H_theta_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    X * (ActualGreenPrimitive.greenHq p hp).derivative = squareQ p - 1 := by
  rw [ActualGreenPrimitive.greenHq, ActualGreenPrimitive.greenHIntegral_value]
  simpa only [actual_low_square_origin_Q p hp, C_1] using
    ActualGreenPrimitive.rational_unitEuler_theta p (squareQ p)
      ((actual_squareQ_degree p hp).trans_lt (by omega))

theorem cubic_Q_dlogQ_cleared :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
      D (invert WPActualPullbackSource.Vpolynomial.toLaurent) =
      3 * T (-1) * (4 - 11 * T 1) * invert WPActualPullbackSource.Vpolynomial.toLaurent := by
  let A : ℚ[X] := WPFiniteZSource.Abar
  let V := WPActualPullbackSource.Vpolynomial
  let c : ℚ[X] := 4 * X - 11
  have hv : A * V.derivative = -3 * c * V := by
    simp only [A, V, c, WPFiniteZSource.Abar,
      WPActualPullbackSource.Vpolynomial, pow_two, derivative_mul,
      derivative_C, derivative_X, derivative_sub, derivative_ofNat, derivative_one,
      zero_sub]
    ring
  have ht : (T (-1) : ℚ[T;T⁻¹]) * T 1 = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hc : invert c.toLaurent = T (-1) * (4 - 11 * T 1) := by
    simp only [c, map_sub, map_mul, map_ofNat, Polynomial.toLaurent_X, invert_T]
    linear_combination 11 * ht
  have h := congrArg (fun P : ℚ[X] => invert P.toLaurent) hv
  simp only [map_mul, map_neg, map_ofNat] at h
  rw [show A = (WPFiniteZSource.Abar : ℚ[X]) by rfl,
    actualAbarQ_invert, hc] at h
  change A.toLaurent * D (invert V.toLaurent) =
    3 * T (-1) * (4 - 11 * T 1) * invert V.toLaurent
  rw [D_invert, D_toLaurent]
  linear_combination -h

theorem actual_HQ_Euler_cleared (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent * D (greenHAtQ p hp) =
      3 * T (-1) * (4 - 11 * T 1) * (invert (lowFpullQ p) - 1) := by
  let H := ActualGreenPrimitive.greenHq p hp
  let Q := invert WPActualPullbackSource.Vpolynomial.toLaurent
  have ht := congrArg (Polynomial.eval₂RingHom LaurentPolynomial.C Q)
    (actual_low_H_theta_Q p hp)
  have ht' : Q * WPActualChiSource.substituteOver H.derivative Q =
      WPActualChiSource.substituteOver (squareQ p) Q - 1 := by
    simpa only [Polynomial.coe_eval₂RingHom, map_mul, map_sub, map_one,
      Polynomial.eval₂_X, WPActualChiSource.substituteOver, H] using ht
  have hf : WPActualChiSource.substituteOver (squareQ p) Q =
      invert (lowFpullQ p) := by
    dsimp only [Q, lowFpullQ]
    rw [← WPActualChiSource.substituteOver_invert,
      WPActualChiSource.substituteOver_toLaurent]
  have he : Q * WPActualChiSource.substituteOver H.derivative Q =
      invert (lowFpullQ p) - 1 := by
    rw [hf] at ht'
    exact ht'
  have hh : greenHAtQ p hp = WPActualChiSource.substituteOver H Q := by
    rw [greenHAtQ, ← WPActualChiSource.substituteOver_toLaurent,
      WPActualChiSource.substituteOver_invert]
  have hd : D (greenHAtQ p hp) =
      WPActualChiSource.substituteOver H.derivative Q * D Q := by
    have hQ : (NativeScalarRows.originalQ : ℚ[T;T⁻¹]) = Q := by
      rw [NativeScalarRows.originalQ, actual_Qrev_eq_V]
    rw [hh]
    rw [← hQ, ActualLowEuler.D_substitute_originalQ]
  rw [hd]
  have hq := cubic_Q_dlogQ_cleared
  change (WPFiniteZSource.Abar : ℚ[X]).toLaurent * D Q =
    3 * T (-1) * (4 - 11 * T 1) * Q at hq
  linear_combination WPActualChiSource.substituteOver H.derivative Q * hq +
    3 * T (-1) * (4 - 11 * T 1) * he

/-- Exact unshifted Euler integration in the original infinity orientation. -/
theorem actual_HQ_log_IBP (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    -resInfinity (greenHAtQ p hp * D (finiteConicLogQ p).toLaurent) =
      dlogQtrace ((finiteConicLogQ p).toLaurent * (invert (lowFpullQ p) - 1)) := by
  have h := congrArg inverseAtrace
    (congrArg (fun L : ℚ[T;T⁻¹] => (finiteConicLogQ p).toLaurent * L)
      (actual_HQ_Euler_cleared p hp))
  have hleft : (finiteConicLogQ p).toLaurent *
      ((WPFiniteZSource.Abar : ℚ[X]).toLaurent * D (greenHAtQ p hp)) =
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent *
        ((finiteConicLogQ p).toLaurent * D (greenHAtQ p hp)) := by ring
  rw [hleft, inverseAtrace_Abar, resInfinity_IBP] at h
  change -resInfinity (greenHAtQ p hp * D (finiteConicLogQ p).toLaurent) = _ at h
  rw [dlogQtrace_apply]
  exact h.trans (congrArg inverseAtrace (by ring))

/-- The original rational defect, including its literal factor p. -/
theorem actual_low_reflection_source_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    lowFpullQ p - T (((p - 1) / 2 : ℕ) : ℤ) * invert (lowFpullQ p) =
      LaurentPolynomial.C (p : ℚ) * lowReflectionDefectQ p hp := by
  have h := congrArg
    (WPActualChiSource.coefficientMap (WPPIntegralReduction.integralRationals p).subtype)
    (actual_low_reflection_defect_source p hp)
  simpa only [actualLowReflectionNumeratorIntegral, weightedReflectionDifference,
    map_sub, map_mul, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert, WPActualChiSource.coefficientMap_C,
    WPActualChiSource.coefficientMap_toLaurent, Polynomial.map_comp,
    squareQIntegral_value p hp, WPHasseIntegralTransport.integralV_map_rational,
    map_natCast, lowFpullQ, lowReflectionDefectQ] using h

/-- SB101d is a whole rational trace identity before division or reduction. -/
theorem reflection_pairing_exact (N : ℕ) (c : ℚ)
    (f e delta : ℚ[T;T⁻¹])
    (h : f - T (N : ℤ) * invert f = LaurentPolynomial.C c * delta) :
    -dlogQtrace (T (-(N : ℤ)) * f * e) +
      dlogQtrace (e * (invert f - 1)) =
      -c * dlogQtrace (T (-(N : ℤ)) * delta * e) - dlogQtrace e := by
  have ht : (T (-(N : ℤ)) : ℚ[T;T⁻¹]) * T (N : ℤ) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have he : T (-(N : ℤ)) * f * e =
      e * invert f + LaurentPolynomial.C c * (T (-(N : ℤ)) * delta * e) := by
    linear_combination T (-(N : ℤ)) * e * h + e * invert f * ht
  rw [he, map_add, dlogQtrace_C_mul, mul_sub, mul_one, map_sub]
  ring

theorem actual_period_trace_carry_cancellation
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    -dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowFpullQ p *
      (finiteConicLogQ p).toLaurent) +
      dlogQtrace ((finiteConicLogQ p).toLaurent * (invert (lowFpullQ p) - 1)) =
      -(p : ℚ) * dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        lowReflectionDefectQ p hp * (finiteConicLogQ p).toLaurent) -
      dlogQtrace (finiteConicLogQ p).toLaurent :=
  reflection_pairing_exact ((p - 1) / 2) (p : ℚ) (lowFpullQ p)
    (finiteConicLogQ p).toLaurent (lowReflectionDefectQ p hp)
    (actual_low_reflection_source_Q p hp)

/-- The first trace is the original native I0 projection, not a field relift. -/
theorem actual_period_log_trace_projection (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowFpullQ p *
      (finiteConicLogQ p).toLaurent) =
      WPFieldAssembly.ResidualProjection.Ij p 0
        (squareQ p * (finiteEvenSquaredQ p).comp (1 - X)) := by
  have he : ((squareQ p * (finiteEvenSquaredQ p).comp (1 - X)).comp
      WPActualPullbackSource.Vpolynomial).toLaurent =
      lowFpullQ p * (finiteConicLogQ p).toLaurent := by
    simp only [mul_comp, comp_assoc, sub_comp, one_comp, X_comp,
      map_mul, lowFpullQ, finiteConicLogQ]
  have h := original_polynomial_dlogQ_projection ((p - 1) / 2)
    (by omega : 0 < (p - 1) / 2) (squareQ p * (finiteEvenSquaredQ p).comp (1 - X))
  rw [he] at h
  simpa only [WPFieldAssembly.ResidualProjection.Ij, Nat.zero_mul, Nat.add_zero,
    mul_assoc] using h

end WPFieldAssembly.ActualGreenCommonTrace
