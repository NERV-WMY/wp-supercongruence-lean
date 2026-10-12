import WPFieldAssembly.ActualGreenCommonTrace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualGreenCommonTrace WPFieldAssembly.ActualBalancedGreenTransfer
  WPFieldAssembly.ActualJointGreen WPFieldAssembly.NativeOriginalResidues
  WPFieldAssembly.ActualDeltaUNextSource WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.ActualCauchyMoment WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ActualBalancedCarry WPFiniteCarry

namespace WPFieldAssembly.ActualSB101Trace

set_option maxHeartbeats 1600000

/-- The literal K_w trace, retaining Abar^p as its denominator. -/
noncomputable def kwTraceQ (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (LaurentPoleTrace.trace p).comp
    ({
      toFun := fun L => LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) *
        T (p : ℤ) * (4 * T 1 - 11) ^ p * L
      map_add' := by intro L M; ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem kwTraceQ_apply (p : ℕ) (L : ℚ[T;T⁻¹]) :
    kwTraceQ p L = LaurentPoleTrace.trace p
      (LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) *
        T (p : ℤ) * (4 * T 1 - 11) ^ p * L) := rfl

noncomputable def actualBSourceQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C ((1 / 2 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) *
    T (-(p : ℤ)) * (ActualGreenPrimitive.greenCoordinateQ p).toLaurent ^ ((p - 1) / 2) *
    (1 - T (-(((p - 1) / 2 : ℕ) : ℤ))) *
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ^ (p - 1)

theorem kw_B_scalar (p : ℕ) :
    (3 * (5 : ℚ) ^ (p - 1)) *
      ((1 / 2 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1))) =
      (3 / 2 : ℚ) * (1 / 5 : ℚ) ^ (p - 1) := by
  have h : (5 : ℚ) ^ (p - 1) * (1 / 5 : ℚ) ^ (p - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [Nat.mul_comm 2 (p - 1), pow_mul]
  linear_combination (3 / 2 : ℚ) * (1 / 5 : ℚ) ^ (p - 1) * h

/-- SB101c after the honest cancellation of Abar^(p-1), still over Q. -/
theorem actual_Kw_Bsource_trace (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    kwTraceQ p (greenHAtQ p hp * actualBSourceQ p) =
      -resInfinity (greenHAtQ p hp * D (finiteConicLogQ p).toLaurent) +
      resInfinity (T (-(((p - 1) / 2 : ℕ) : ℤ)) * greenHAtQ p hp *
        D (finiteConicLogQ p).toLaurent) -
      (1 / 2 : ℚ) * dlogVtrace (greenHAtQ p hp) +
      (1 / 2 : ℚ) * dlogVtrace
        (T (-(((p - 1) / 2 : ℕ) : ℤ)) * greenHAtQ p hp) := by
  let u : ℚ[T;T⁻¹] := T (-(((p - 1) / 2 : ℕ) : ℤ))
  let H := greenHAtQ p hp
  let E := (finiteConicLogQ p).toLaurent
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let s := (ActualGreenPrimitive.greenCoordinateQ p).toLaurent
  let c : ℚ[T;T⁻¹] := 4 * T 1 - 11
  let L := LaurentPolynomial.C ((3 / 2 : ℚ) * (1 / 5 : ℚ) ^ (p - 1)) *
    s ^ ((p - 1) / 2) * c ^ p * (1 - u) * H
  have ht : (T (p : ℤ) : ℚ[T;T⁻¹]) * T (-(p : ℤ)) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hnum : LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * T (p : ℤ) *
      c ^ p * (H * actualBSourceQ p) = A ^ (p - 1) * L := by
    unfold actualBSourceQ
    calc
      _ = (LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) *
          LaurentPolynomial.C ((1 / 2 : ℚ) * (1 / 5 : ℚ) ^ (2 * (p - 1)))) *
          (T (p : ℤ) * T (-(p : ℤ))) * c ^ p * s ^ ((p - 1) / 2) *
          (1 - u) * A ^ (p - 1) * H := by ring
      _ = _ := by rw [← map_mul, kw_B_scalar, ht]; dsimp only [L]; ring
  have hclear : kwTraceQ p (H * actualBSourceQ p) = inverseAtrace L := by
    rw [kwTraceQ_apply, hnum]
    have hc := LaurentPoleTrace.trace_cleared_pow 1 (p - 1) L
    rw [show 1 + (p - 1) = p by omega, pole_Abar_eq] at hc
    exact hc.trans (trace_one_eq_inverseAtrace L)
  have hs := congrArg (fun P : ℚ[X] => P.toLaurent)
    (actual_finite_conic_log_Abar_source p hp)
  simp only [map_sub, map_mul, map_ofNat, map_pow,
    Polynomial.toLaurent_X, ← D_toLaurent] at hs
  have hscalar : (-(3 * Polynomial.C (1 / 5 : ℚ) ^ (p - 1)) : ℚ[X]).toLaurent =
      -LaurentPolynomial.C (3 * (1 / 5 : ℚ) ^ (p - 1)) := by
    rw [← Polynomial.C_pow,
      show (3 : ℚ[X]) = Polynomial.C (3 : ℚ) by simp only [map_ofNat],
      ← Polynomial.C_mul, map_neg, Polynomial.toLaurent_C]
  rw [hscalar] at hs
  have hL : L = -(A * ((1 - u) * H * D E)) -
      LaurentPolynomial.C (1 / 2 : ℚ) * ((33 - 12 * T 1) * (1 - u) * H) := by
    change 2 * A * D E - 3 * c =
      -LaurentPolynomial.C (3 * (1 / 5 : ℚ) ^ (p - 1)) *
        s ^ ((p - 1) / 2) * c ^ p at hs
    have hhalf : (LaurentPolynomial.C ((3 / 2 : ℚ) * (1 / 5 : ℚ) ^ (p - 1)) :
        ℚ[T;T⁻¹]) = LaurentPolynomial.C (1 / 2 : ℚ) *
          LaurentPolynomial.C (3 * (1 / 5 : ℚ) ^ (p - 1)) := by
      rw [← map_mul]
      congr 1
      ring
    have hunit : (LaurentPolynomial.C (1 / 2 : ℚ) : ℚ[T;T⁻¹]) * 2 = 1 := by
      rw [show (2 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (2 : ℚ) by
        simp only [map_ofNat],
        ← map_mul, show (1 / 2 : ℚ) * 2 = 1 by norm_num, map_one]
    dsimp only [L, c]
    rw [hhalf]
    dsimp only [c] at hs
    linear_combination LaurentPolynomial.C (1 / 2 : ℚ) * (1 - u) * H * hs -
      A * ((1 - u) * H * D E) * hunit
  have hD : (1 - u) * H * D E = H * D E - u * H * D E := by ring
  have hV : (33 - 12 * T 1) * (1 - u) * H =
      (33 - 12 * T 1) * H - (33 - 12 * T 1) * (u * H) := by ring
  rw [hclear, hL, map_sub, map_neg, inverseAtrace_Abar,
    inverseAtrace_C_mul, hD, resInfinity_sub, hV, map_sub]
  change _ = -resInfinity (H * D E) + resInfinity (u * H * D E) -
    (1 / 2 : ℚ) * inverseAtrace ((33 - 12 * T 1) * H) +
    (1 / 2 : ℚ) * inverseAtrace ((33 - 12 * T 1) * (u * H))
  ring

theorem actual_Kw_Bsource_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    kwTraceQ p (greenHAtQ p hp * actualBSourceQ p) =
      -resInfinity (greenHAtQ p hp * D (finiteConicLogQ p).toLaurent) +
      resInfinity (T (-(((p - 1) / 2 : ℕ) : ℤ)) * greenHAtQ p hp *
        D (finiteConicLogQ p).toLaurent) +
      (3 / 2 : ℚ) * (ActualGreenPrimitive.greenHq p hp).eval (4 / 125) := by
  rw [actual_Kw_Bsource_trace p hp, actual_Euler_dlogV_endpoint p hp,
    greenHAtQ, shifted_inverted_polynomial_dlogVtrace_zero ((p - 1) / 2) (by omega)]
  ring

noncomputable def unitPairQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ :=
  (metricStar p hp).val * QO p (WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2 *
    unitWindow ((p : ℚ) / 3) ((p - 1) / 2))

/-- NC117's post-HF numerator; the common-source correction is kept separately. -/
noncomputable def qStarQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ :=
  unitPairQ p hp - dlogQtrace (greenProperTraceNumeratorQ p hp) -
    (3 / 2 : ℚ) * (ActualGreenPrimitive.greenHq p hp).eval (4 / 125) -
    3 * WPFirstResidue.LiteralNormalization.literalR0 p +
    kwTraceQ p (greenHAtQ p hp * actualBSourceQ p) -
    weightedDlogQtrace p (ActualBalancedTrace.comparisonRational p hp)

noncomputable def vBalancedQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ :=
  -dlogQtrace (finiteConicLogQ p).toLaurent -
    weightedDlogQtrace p (ActualBalancedTrace.comparisonRational p hp) -
    3 * WPFirstResidue.LiteralNormalization.literalR0 p +
    2 * (WPPIntegralReduction.integralRationals p).subtype
      ((ActualBalancedCarry.balancedProperIntegral p hp).eval 1) *
      (finiteLogCIntegral p hp).val

theorem actual_full_log_period_pair (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualCauchyTbarAttachment.fullLogPairNumerator p hp =
      unitPairQ p hp + dlogQtrace
        (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowFpullQ p *
          (finiteConicLogQ p).toLaurent) := by
  let Y := WPActualRankTwoParameter.rankJacobiNode p 1
  let F := squareQ p
  let E := (finiteEvenSquaredQ p).comp (1 - X)
  have he : (F * E).comp (1 - X ^ 2) = Y ^ 2 * finiteEvenLogQ p := by
    rw [mul_comp, actual_low_square_pullback_Q p hp]
    dsimp only [E]
    rw [comp_assoc]
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel]
    rw [finiteEvenSquaredQ_pullback]
  have hq : QO p (Y ^ 2 * finiteEvenLogQ p) = ResidualProjection.Ij p 0 (F * E) := by
    rw [← he, QO, quadraticInverse_quadratic]
  have hz : QO p (Y ^ 2) = 0 :=
    ResidualProjection.low_correction_both_projections_zero p hp F
      (actual_squareQ_degree p hp) 0
  have hsplit : QO p (Y ^ 2 * finiteEvenLogQ p) =
      QO p (Y ^ 2 * (rationalBinomialLog ((p - 1) / 2)).comp
        (1 - X ^ 2)) := by
    rw [finiteEvenLogQ, mul_sub, QO_sub_local,
      show Y ^ 2 * Polynomial.C ((rationalBinomialLog ((p - 1) / 2)).eval 1) =
        Polynomial.C ((rationalBinomialLog ((p - 1) / 2)).eval 1) * Y ^ 2 by ring,
      QO_C_mul, hz, mul_zero, sub_zero]
  rw [actual_period_log_trace_projection p hp, ← hq, hsplit]
  unfold ActualCauchyTbarAttachment.fullLogPairNumerator unitPairQ
  rw [mul_add, QO_add]
  have hm : Y ^ 2 * (Polynomial.C (metricStar p hp).val *
        unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) =
      Polynomial.C (metricStar p hp).val *
        (Y ^ 2 * unitWindow ((p : ℚ) / 3) ((p - 1) / 2)) := by ring
  rw [hm, QO_C_mul]
  ring

/-- SB101b before p-division, retaining its actual reflection and metric carries. -/
theorem actual_SB101b_before_division (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    qStarQ p hp = vBalancedQ p hp +
      ActualCauchyTbarAttachment.fullLogPairNumerator p hp -
      (p : ℚ) * dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        lowReflectionDefectQ p hp * (finiteConicLogQ p).toLaurent) -
      (p : ℚ) / 2 * (ActualGreenPrimitive.greenOriginMetricIntegral p hp).val := by
  have hk := actual_Kw_Bsource_endpoint p hp
  have hi := actual_HQ_log_IBP p hp
  have hr := actual_period_trace_carry_cancellation p hp
  have he := actual_SB101e p hp
  have hl := actual_full_log_period_pair p hp
  unfold qStarQ vBalancedQ
  linear_combination hk + hi + hr + he - hl

end WPFieldAssembly.ActualSB101Trace
