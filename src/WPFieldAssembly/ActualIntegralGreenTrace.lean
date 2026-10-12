import WPFieldAssembly.ActualSigmaIntegral
import WPFieldAssembly.LaurentPoleIntegral

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSigmaIntegral WPFieldAssembly.ActualHFTransmutation
  WPFieldAssembly.ActualSB101Trace WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.ActualBalancedGreenTransfer WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen WPPIntegralReduction WPActualEtaIntegrality
  WPActualRankTwoHatLift

namespace WPFieldAssembly.ActualIntegralGreenTrace

set_option maxHeartbeats 1600000

theorem invert_integral (p : ℕ) [Fact p.Prime] (L : ℚ[T;T⁻¹])
    (hL : L ∈ integralLaurent p) : invert L ∈ integralLaurent p := by
  intro j
  rw [invert_apply]
  exact hL (-j)

theorem c_integral (p : ℕ) [Fact p.Prime] :
    (4 * T 1 - 11 : ℚ[T;T⁻¹]) ∈ integralLaurent p :=
  (integralLaurent p).sub_mem
    ((integralLaurent p).mul_mem (natCast_mem (integralLaurent p) 4) (integral_T p 1))
    (natCast_mem (integralLaurent p) 11)

theorem Abar_integral (p : ℕ) [Fact p.Prime] :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent ∈ integralLaurent p := by
  have h := mapped_integral p (actualAbarIntegral p).toLaurent
  simpa only [WPActualChiSource.coefficientMap_toLaurent, actualAbarIntegral,
    WPFiniteZSource.Abar, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one] using h

theorem kwNumerator_integral (p : ℕ) [Fact p.Prime] :
    kwNumeratorQ p ∈ integralLaurent p := by
  unfold kwNumeratorQ
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem
      (integral_C p _ ((integralRationals p).mul_mem (natCast_mem (integralRationals p) 3)
        ((integralRationals p).pow_mem (natCast_mem (integralRationals p) 5) (p - 1))))
      (integral_T p p)) ((integralLaurent p).pow_mem (c_integral p) p)

theorem kwDerivativeNumerator_integral (p : ℕ) [Fact p.Prime] :
    kwDerivativeNumeratorQ p ∈ integralLaurent p := by
  unfold kwDerivativeNumeratorQ
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem
      ((integralLaurent p).mul_mem
        (integral_C p _ ((integralRationals p).mul_mem (natCast_mem (integralRationals p) 3)
          ((integralRationals p).pow_mem (natCast_mem (integralRationals p) 5) (p - 1))))
        (integral_T p _)) ((integralLaurent p).pow_mem (c_integral p) (p - 1)))
    ((integralLaurent p).add_mem (c_integral p)
      ((integralLaurent p).mul_mem (natCast_mem (integralLaurent p) 4) (integral_T p 1)))

theorem kwTrace_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) : kwTraceQ p L ∈ integralRationals p :=
  LaurentPoleIntegral.trace_integral p p hp _
    ((integralLaurent p).mul_mem (kwNumerator_integral p) hL)

theorem kwLogTrace_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) : kwLogTraceQ p L ∈ integralRationals p := by
  apply LaurentPoleIntegral.trace_integral p (p + 1) hp
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).sub_mem
      ((integralLaurent p).mul_mem (Abar_integral p) (kwDerivativeNumerator_integral p))
      ((integralLaurent p).mul_mem (kwNumerator_integral p)
        (derivative_integral p _ (Abar_integral p)))) hL

theorem weightedTrace_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) :
    weightedDlogQtrace p L ∈ integralRationals p := by
  apply LaurentPoleIntegral.trace_integral p (p + 1) hp
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem
      ((integralLaurent p).mul_mem
        ((integralLaurent p).mul_mem
          (integral_C p _ ((integralRationals p).mul_mem (natCast_mem (integralRationals p) 9)
            ((integralRationals p).pow_mem (natCast_mem (integralRationals p) 5) (p - 1))))
          (integral_T p _)) ((integralLaurent p).pow_mem (c_integral p) p))
      ((integralLaurent p).sub_mem (natCast_mem (integralLaurent p) 4)
        ((integralLaurent p).mul_mem (natCast_mem (integralLaurent p) 11) (integral_T p 1)))) hL

theorem xiTrace_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) : xiTraceQ p L ∈ integralRationals p :=
  weightedTrace_integral p hp _ ((integralLaurent p).mul_mem (integral_T p _) hL)

theorem dlogQtrace_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (L : ℚ[T;T⁻¹]) (hL : L ∈ integralLaurent p) : dlogQtrace L ∈ integralRationals p := by
  rw [show dlogQtrace L =
    inverseAtrace ((3 : ℚ[T;T⁻¹]) * T (-1) * (4 - 11 * T 1) * L) from rfl]
  rw [← trace_one_eq_inverseAtrace]
  apply LaurentPoleIntegral.trace_integral p 1 hp
  exact (integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem
      ((integralLaurent p).mul_mem (natCast_mem (integralLaurent p) 3) (integral_T p (-1)))
      ((integralLaurent p).sub_mem (natCast_mem (integralLaurent p) 4)
        ((integralLaurent p).mul_mem (natCast_mem (integralLaurent p) 11) (integral_T p 1)))) hL

theorem greenHAtQ_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    greenHAtQ p hp ∈ integralLaurent p := by
  let H := (ActualGreenPrimitive.greenHIntegral p hp).comp
    (WPHasseIntegralTransport.integralV p (by omega))
  have hm : WPActualChiSource.coefficientMap (integralRationals p).subtype H.toLaurent =
      ((ActualGreenPrimitive.greenHq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent := by
    simp only [H, WPActualChiSource.coefficientMap_toLaurent, Polynomial.map_comp,
      WPHasseIntegralTransport.integralV_map_rational, ActualGreenPrimitive.greenHq]
  rw [greenHAtQ, ← hm]
  exact invert_integral p _ (mapped_integral p H.toLaurent)

theorem finiteConicLog_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (finiteConicLogQ p).toLaurent ∈ integralLaurent p := by
  have h := mapped_integral p (finiteConicLogIntegral p hp).toLaurent
  simpa only [WPActualChiSource.coefficientMap_toLaurent, finiteConicLogIntegral_value p hp] using h

theorem periodCarry_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowReflectionDefectQ p hp *
      (finiteConicLogQ p).toLaurent) ∈ integralRationals p :=
  dlogQtrace_integral p hp _ ((integralLaurent p).mul_mem
    ((integralLaurent p).mul_mem (integral_T p _)
      (mapped_integral p (actualReflectionDefectIntegral p hp))) (finiteConicLog_integral p hp))

theorem balancedBrace_div_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    balancedBraceQ p hp / (p : ℚ) ∈ integralRationals p := by
  have he : balancedBraceQ p hp / (p : ℚ) =
      3 * (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp).val -
        xiTraceQ p (actualBalancedDividedQ p hp) := by
    rw [ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral_value p hp]
    have h := actual_SB98b_before_division p hp
    field_simp [show (p : ℚ) ≠ 0 by positivity]
    linear_combination -h
  rw [he]
  exact (integralRationals p).sub_mem
    ((integralRationals p).mul_mem (natCast_mem (integralRationals p) 3)
      (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp).property)
    (xiTrace_integral p hp _ (actualBalancedDividedQ_integral p hp))

theorem qStar_div_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    qStarQ p hp / (p : ℚ) ∈ integralRationals p := by
  have he : qStarQ p hp / (p : ℚ) = balancedBraceQ p hp / (p : ℚ) -
      (kwTraceQ p (greenHAtQ p hp * actualSigmaQ p hp) +
        kwLogTraceQ p (greenHAtQ p hp * comparisonRational p hp)) := by
    have h := actual_HF_transmutation_before_division p hp
    field_simp [show (p : ℚ) ≠ 0 by positivity]
    linear_combination -h
  rw [he]
  exact (integralRationals p).sub_mem (balancedBrace_div_integral p hp)
    ((integralRationals p).add_mem
      (kwTrace_integral p hp _ ((integralLaurent p).mul_mem (greenHAtQ_integral p hp)
        (actualSigmaQ_integral p hp)))
      (kwLogTrace_integral p hp _ ((integralLaurent p).mul_mem (greenHAtQ_integral p hp)
        (mapped_integral p (comparisonIntegral p)))))

theorem vBalanced_div_integral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    vBalancedQ p hp / (p : ℚ) ∈ integralRationals p := by
  have he : vBalancedQ p hp / (p : ℚ) = qStarQ p hp / (p : ℚ) -
      (ActualCauchyTbarAttachment.fullLogDividedIntegral p hp).val +
      dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowReflectionDefectQ p hp *
        (finiteConicLogQ p).toLaurent) +
      (1 / 2 : ℚ) * (ActualGreenPrimitive.greenOriginMetricIntegral p hp).val := by
    rw [ActualCauchyTbarAttachment.fullLogDividedIntegral_value p hp]
    have h := actual_SB101b_before_division p hp
    field_simp [show (p : ℚ) ≠ 0 by positivity]
    linear_combination -2 * h
  rw [he]
  have hh : (1 / 2 : ℚ) ∈ integralRationals p := by
    have hv := (smallIntegralInverse p 2).property
    simpa only [smallIntegralInverse_value p 2 (by omega) (by omega), Nat.cast_ofNat] using hv
  exact (integralRationals p).add_mem
    ((integralRationals p).add_mem
      ((integralRationals p).sub_mem (qStar_div_integral p hp)
        (ActualCauchyTbarAttachment.fullLogDividedIntegral p hp).property)
      (periodCarry_integral p hp))
    ((integralRationals p).mul_mem hh (ActualGreenPrimitive.greenOriginMetricIntegral p hp).property)

noncomputable def qStarDividedIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p := ⟨qStarQ p hp / (p : ℚ), qStar_div_integral p hp⟩

noncomputable def vBalancedDividedIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p := ⟨vBalancedQ p hp / (p : ℚ), vBalanced_div_integral p hp⟩

noncomputable def periodCarryIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowReflectionDefectQ p hp *
    (finiteConicLogQ p).toLaurent), periodCarry_integral p hp⟩

/-- The original SB101 quotient now lives in the actual integral ring before reduction. -/
theorem actual_SB101_integral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    qStarDividedIntegral p hp = vBalancedDividedIntegral p hp +
      ActualCauchyTbarAttachment.fullLogDividedIntegral p hp - periodCarryIntegral p hp -
      smallIntegralInverse p 2 * ActualGreenPrimitive.greenOriginMetricIntegral p hp := by
  apply Subtype.ext
  change qStarQ p hp / (p : ℚ) = vBalancedQ p hp / (p : ℚ) +
    (ActualCauchyTbarAttachment.fullLogDividedIntegral p hp).val -
      dlogQtrace (T (-(((p - 1) / 2 : ℕ) : ℤ)) * lowReflectionDefectQ p hp *
        (finiteConicLogQ p).toLaurent) -
      (smallIntegralInverse p 2).val * (ActualGreenPrimitive.greenOriginMetricIntegral p hp).val
  rw [smallIntegralInverse_value p 2 (by omega) (by omega),
    ActualCauchyTbarAttachment.fullLogDividedIntegral_value p hp]
  have h := actual_SB101b_before_division p hp
  field_simp [show (p : ℚ) ≠ 0 by positivity]
  linear_combination 2 * h

theorem actual_SB101_field_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (qStarDividedIntegral p hp) = residueHom p (vBalancedDividedIntegral p hp) -
      ActualDeltaUNextSource.QO p (WPActualRankTwoLegendreField.actualLegendreJacobi p ^ 2 *
        ActualJointGreen.actualTbarP p) - residueHom p (periodCarryIntegral p hp) -
      (1 / 2 : ZMod p) * residueHom p (ActualGreenPrimitive.greenOriginMetricIntegral p hp) := by
  have h := congrArg (residueHom p) (actual_SB101_integral_source p hp)
  rw [map_sub, map_sub, map_add, map_mul, smallIntegralInverse_field p 2 (by omega) (by omega),
    ActualCauchyTbarAttachment.actual_SB82d p hp] at h
  linear_combination h

noncomputable def balancedTraceIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : integralRationals p :=
  ⟨xiTraceQ p (actualBalancedDividedQ p hp),
    xiTrace_integral p hp _ (actualBalancedDividedQ_integral p hp)⟩

noncomputable def commonSourceTraceIntegral (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    integralRationals p :=
  ⟨kwTraceQ p (greenHAtQ p hp * actualSigmaQ p hp) +
    kwLogTraceQ p (greenHAtQ p hp * comparisonRational p hp),
    (integralRationals p).add_mem
      (kwTrace_integral p hp _ ((integralLaurent p).mul_mem (greenHAtQ_integral p hp)
        (actualSigmaQ_integral p hp)))
      (kwLogTrace_integral p hp _ ((integralLaurent p).mul_mem (greenHAtQ_integral p hp)
        (mapped_integral p (comparisonIntegral p))))⟩

/-- Both actual trace terms accompany the actual leading Cauchy digit. -/
theorem actual_coupled_trace_integral_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    3 * ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp =
      qStarDividedIntegral p hp + commonSourceTraceIntegral p hp + balancedTraceIntegral p hp := by
  apply Subtype.ext
  change 3 * (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp).val =
    qStarQ p hp / (p : ℚ) +
      (kwTraceQ p (greenHAtQ p hp * actualSigmaQ p hp) +
        kwLogTraceQ p (greenHAtQ p hp * comparisonRational p hp)) +
      xiTraceQ p (actualBalancedDividedQ p hp)
  rw [ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral_value p hp]
  have h98 := actual_SB98b_before_division p hp
  have hHF := actual_HF_transmutation_before_division p hp
  field_simp [show (p : ℚ) ≠ 0 by positivity]
  linear_combination h98 + hHF

theorem actual_coupled_trace_field_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    3 * residueHom p (ActualCauchyTbarAttachment.coupledCauchyNormDigitIntegral p hp) =
      residueHom p (qStarDividedIntegral p hp) + residueHom p (commonSourceTraceIntegral p hp) +
        residueHom p (balancedTraceIntegral p hp) := by
  have h := congrArg (residueHom p) (actual_coupled_trace_integral_source p hp)
  simpa only [map_mul, map_ofNat, map_add] using h

end WPFieldAssembly.ActualIntegralGreenTrace
