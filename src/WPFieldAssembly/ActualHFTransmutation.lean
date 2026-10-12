import WPFieldAssembly.ActualSB101Trace

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSB101Trace WPFieldAssembly.ActualGreenCommonTrace
  WPFieldAssembly.ActualBalancedGreenTransfer WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualJointGreen WPFieldAssembly.NativeOriginalResidues

namespace WPFieldAssembly.ActualHFTransmutation

set_option maxHeartbeats 1600000

noncomputable def kwNumeratorQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * T (p : ℤ) * (4 * T 1 - 11) ^ p

noncomputable def kwDerivativeNumeratorQ (p : ℕ) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * T ((p : ℤ) - 1) *
    (4 * T 1 - 11) ^ (p - 1) * ((4 * T 1 - 11) + 4 * T 1)

/-- K_w dlog(x(4x-11)/Abar), with all poles kept in the common denominator. -/
noncomputable def kwLogTraceQ (p : ℕ) : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ :=
  (LaurentPoleTrace.trace (p + 1)).comp
    ({
      toFun := fun L => ((WPFiniteZSource.Abar : ℚ[X]).toLaurent *
          kwDerivativeNumeratorQ p - kwNumeratorQ p *
          D (WPFiniteZSource.Abar : ℚ[X]).toLaurent) * L
      map_add' := by intro L M; ring
      map_smul' := by
        intro a L
        simp only [LaurentPolynomial.smul_eq_C_mul, RingHom.id_apply]
        ring
    } : ℚ[T;T⁻¹] →ₗ[ℚ] ℚ[T;T⁻¹])

private theorem D_pow_succ (L : ℚ[T;T⁻¹]) (n : ℕ) :
    D (L ^ (n + 1)) = LaurentPolynomial.C ((n + 1 : ℕ) : ℚ) * L ^ n * D L := by
  exact ActualBalancedGreenTransfer.D_pow_nat L n

theorem kwNumerator_derivative (p : ℕ) (hp : 0 < p) :
    D (kwNumeratorQ p) = LaurentPolynomial.C (p : ℚ) * kwDerivativeNumeratorQ p := by
  let c : ℚ[T;T⁻¹] := 4 * T 1 - 11
  have hT : D (T (p : ℤ) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (p : ℚ) * T ((p : ℤ) - 1) := by
    simpa only [map_one, one_mul, Int.cast_natCast] using D_monomial (1 : ℚ) (p : ℤ)
  have h1 : D (T (1 : ℤ) : ℚ[T;T⁻¹]) = 1 := by
    simpa using D_monomial (1 : ℚ) (1 : ℤ)
  have hc : D c = LaurentPolynomial.C (4 : ℚ) := by
    change D (LaurentPolynomial.C (4 : ℚ) * T 1 - LaurentPolynomial.C 11) = _
    rw [map_sub, D_C_mul, h1, D_C, mul_one, sub_zero]
  have hn : (p - 1) + 1 = p := by omega
  have hd := D_pow_succ c (p - 1)
  rw [hn, hc] at hd
  have ht : (T ((p : ℤ) - 1) : ℚ[T;T⁻¹]) * T 1 = T (p : ℤ) := by
    rw [← T_add, sub_add_cancel]
  have hpow : c ^ p = c ^ (p - 1) * c := by rw [← pow_succ, hn]
  unfold kwNumeratorQ kwDerivativeNumeratorQ
  rw [show LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * T (p : ℤ) * c ^ p =
    LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * (T (p : ℤ) * c ^ p) by ring]
  rw [D_C_mul, D_mul, hT, hd, hpow, ← ht]
  simp only [map_mul, map_ofNat]
  dsimp only [c]
  ring

theorem actual_kw_IBP (p : ℕ) (hp : 0 < p) (H S : ℚ[T;T⁻¹]) :
    kwTraceQ p (D H * S) + kwTraceQ p (H * D S) =
      -(p : ℚ) * kwLogTraceQ p (H * S) := by
  let N := kwNumeratorQ p
  let N1 := kwDerivativeNumeratorQ p
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  have h := LaurentPoleTrace.trace_D p (N * (H * S))
  rw [D_mul, D_mul, kwNumerator_derivative p hp] at h
  have hsrc : LaurentPolynomial.C (p : ℚ) * N1 * (H * S) +
      N * (D H * S + H * D S) =
      LaurentPolynomial.C (p : ℚ) * (N1 * H * S) +
        N * (D H * S) + N * (H * D S) := by ring
  rw [hsrc, map_add, map_add, LaurentPoleTrace.trace_C_mul] at h
  have hc := LaurentPoleTrace.trace_cleared p (N1 * H * S)
  rw [pole_Abar_eq] at hc
  have hn : (A * N1 - N * D A) * (H * S) =
      A * (N1 * H * S) - N * (H * S) * D A := by ring
  change LaurentPoleTrace.trace p (N * (D H * S)) +
      LaurentPoleTrace.trace p (N * (H * D S)) =
    -(p : ℚ) * LaurentPoleTrace.trace (p + 1) ((A * N1 - N * D A) * (H * S))
  rw [hn, map_sub, hc]
  rw [pole_Abar_eq] at h
  linear_combination h

theorem actual_HF_weighted_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (S : ℚ[T;T⁻¹]) :
    weightedDlogQtrace p (invert (lowFpullQ p) * S) =
      weightedDlogQtrace p S + kwTraceQ p (D (greenHAtQ p hp) * S) := by
  let A := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  let N := kwNumeratorQ p
  let W : ℚ[T;T⁻¹] := LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) *
    T ((p - 1 : ℕ) : ℤ) * (4 * T 1 - 11) ^ p * (4 - 11 * T 1)
  have ht : (T (p : ℤ) : ℚ[T;T⁻¹]) * T (-1) = T ((p - 1 : ℕ) : ℤ) := by
    rw [← T_add]
    congr 1
    omega
  have hscalar : (LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) : ℚ[T;T⁻¹]) * 3 =
      LaurentPolynomial.C (9 * (5 : ℚ) ^ (p - 1)) := by
    rw [show (3 : ℚ[T;T⁻¹]) = LaurentPolynomial.C (3 : ℚ) by
      simp only [map_ofNat], ← map_mul]
    congr 1
    ring
  have hW : N * (3 * T (-1) * (4 - 11 * T 1)) = W := by
    dsimp only [N, kwNumeratorQ, W]
    calc
      _ = (LaurentPolynomial.C (3 * (5 : ℚ) ^ (p - 1)) * 3) *
          (T (p : ℤ) * T (-1)) * (4 * T 1 - 11) ^ p * (4 - 11 * T 1) := by ring
      _ = _ := by rw [hscalar, ht]
  have hs := actual_HQ_Euler_cleared p hp
  have he : A * (N * (D (greenHAtQ p hp) * S)) =
      W * (invert (lowFpullQ p) * S) - W * S := by
    linear_combination N * S * hs + (invert (lowFpullQ p) - 1) * S * hW
  have h := congrArg (LaurentPoleTrace.trace (p + 1)) he
  rw [map_sub] at h
  have hc := LaurentPoleTrace.trace_cleared p (N * (D (greenHAtQ p hp) * S))
  rw [pole_Abar_eq] at hc
  rw [hc] at h
  change kwTraceQ p (D (greenHAtQ p hp) * S) =
    weightedDlogQtrace p (invert (lowFpullQ p) * S) - weightedDlogQtrace p S at h
  linear_combination -h

/-- The actual divided derivative from SB95, formed over Q before any reduction. -/
noncomputable def actualSigmaQ (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1 / (p : ℚ)) *
    (D (comparisonRational p hp) - actualBSourceQ p)

theorem actual_comparison_derivative_Q (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    D (comparisonRational p hp) = actualBSourceQ p +
      LaurentPolynomial.C (p : ℚ) * actualSigmaQ p hp := by
  have hu : LaurentPolynomial.C (p : ℚ) * LaurentPolynomial.C (1 / (p : ℚ)) =
      (1 : ℚ[T;T⁻¹]) := by
    rw [← map_mul, mul_one_div_cancel (by positivity : (p : ℚ) ≠ 0), map_one]
  unfold actualSigmaQ
  linear_combination -(D (comparisonRational p hp) - actualBSourceQ p) * hu

theorem actual_QH_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualDeltaUNextSource.QH p (WPActualRankTwoParameter.rankJacobiNode p 1 ^ 2) =
      (ActualGreenPrimitive.greenHq p hp).eval (4 / 125) := by
  rw [ActualGreenPrimitive.greenHq, ActualGreenPrimitive.greenHIntegral_value]
  rfl

/-- NC117's exact common-source correction, without asserting an integral quotient value. -/
theorem actual_HF_transmutation_before_division
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    balancedBraceQ p hp = qStarQ p hp + (p : ℚ) *
      (kwTraceQ p (greenHAtQ p hp * actualSigmaQ p hp) +
        kwLogTraceQ p (greenHAtQ p hp * comparisonRational p hp)) := by
  let H := greenHAtQ p hp
  let S := comparisonRational p hp
  have hf := actual_HF_weighted_source p hp S
  have hi := actual_kw_IBP p (by omega) H S
  have hs := congrArg (fun L : ℚ[T;T⁻¹] => kwTraceQ p (H * L))
    (actual_comparison_derivative_Q p hp)
  have hsplit : H * (actualBSourceQ p + LaurentPolynomial.C (p : ℚ) * actualSigmaQ p hp) =
      H * actualBSourceQ p + LaurentPolynomial.C (p : ℚ) * (H * actualSigmaQ p hp) := by ring
  rw [hsplit, map_add] at hs
  have hscale : kwTraceQ p (LaurentPolynomial.C (p : ℚ) * (H * actualSigmaQ p hp)) =
      (p : ℚ) * kwTraceQ p (H * actualSigmaQ p hp) := by
    simpa only [LaurentPolynomial.smul_eq_C_mul, smul_eq_mul] using (kwTraceQ p).map_smul (p : ℚ)
      (H * actualSigmaQ p hp)
  rw [hscale] at hs
  unfold balancedBraceQ qStarQ
  rw [actual_QH_endpoint p hp]
  change _ = unitPairQ p hp - dlogQtrace (greenProperTraceNumeratorQ p hp) -
    (3 / 2 : ℚ) * (ActualGreenPrimitive.greenHq p hp).eval (4 / 125) -
    3 * WPFirstResidue.LiteralNormalization.literalR0 p + kwTraceQ p (H * actualBSourceQ p) -
    weightedDlogQtrace p S + (p : ℚ) *
      (kwTraceQ p (H * actualSigmaQ p hp) + kwLogTraceQ p (H * S))
  dsimp only [unitPairQ]
  linear_combination -hf - hi + hs

end WPFieldAssembly.ActualHFTransmutation
