import WPActualGaussProper

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeJetODE WPActualNativeFirstIntegral
  WPActualCMGauss WPActualCubicGauge WPActualCubicCarrier WPActualCubicHasse

namespace WPActualNativeCubicJet

/-- The complete original J_N, cleared with its actual largest cubic denominator. -/
noncomputable def nativeCubicJet (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  cubicLift ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p)

noncomputable def nativeRatioNumerator (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  cubicH * nativeCubicJet p

theorem nativeCubicJet_degree (p : ℕ) [Fact p.Prime] :
    (nativeCubicJet p).natDegree ≤ 4 * ((p - 1) / 2) := by
  simpa only [nativeCubicJet, show 3 * ((p - 1) / 2) + (p - 1) / 2 = 4 * ((p - 1) / 2) by omega] using
    cubicLift_degree ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p) (by omega)

theorem nativeRatioNumerator_degree (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (nativeRatioNumerator p).natDegree ≤ 2 * p - 1 := by
  have hh : (cubicH : (ZMod p)[X]).natDegree ≤ 1 := by unfold cubicH; compute_degree
  have hd := natDegree_mul_le_of_le hh (nativeCubicJet_degree p)
  have hn := WPActualHasseReciprocal.actual_half_exponent p hp
  change (nativeRatioNumerator p).natDegree ≤ 1 + 4 * ((p - 1) / 2) at hd
  exact hd.trans (by omega)

theorem nativeRatioNumerator_origin (p : ℕ) [Fact p.Prime] :
    (nativeRatioNumerator p).eval 0 = 0 := by
  simp [nativeRatioNumerator, nativeCubicJet, cubicLift_origin, nativeJetField_origin]

theorem nativeRatioNumerator_endpoint (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeRatioNumerator p).eval 1 = 0 := by
  have h9 : (9 : ZMod p) ≠ 0 := by
    exact WPActualGaussProper.small_cast_ne_zero p 9 (by omega) (by omega)
  have hh : (cubicH : (ZMod p)[X]).eval 1 = 9 := by norm_num [cubicH]
  have ha : (cubicA : (ZMod p)[X]).eval 1 = 0 := by simp [cubicA]
  rw [nativeRatioNumerator, eval_mul, nativeCubicJet,
    cubicLift_point_eval ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p) 1
      (nativeJetField_degree p) (by omega) (by rw [hh]; exact h9), ha]
  simp [nativeJetField_origin]

/-- The whole native jet's cleared derivative law, including its original high band. -/
theorem nativeCubicJet_gauge (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicH ^ 4 * (nativeCubicJet p).derivative + 12 * cubicH ^ 3 * nativeCubicJet p =
      cubicB * cubicLift ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p).derivative := by
  have he := cubicLift_derivative ((p - 1) / 2) (3 * ((p - 1) / 2))
    (nativeJetField p) (nativeJetField_degree p) (by omega)
  have hc : 8 * C ((3 * ((p - 1) / 2) : ℕ) : ZMod p) + 12 = 0 := by
    have hh := congrArg (Polynomial.C (R := ZMod p)) (actual_half_gauge p hp)
    simp only [map_add, map_mul, C_ofNat, map_zero] at hh
    simp only [Nat.cast_mul, Nat.cast_ofNat, map_mul, C_ofNat]
    linear_combination 3 * hh
  change cubicH ^ 4 * (nativeCubicJet p).derivative -
      8 * C ((3 * ((p - 1) / 2) : ℕ) : ZMod p) * cubicH ^ 3 * nativeCubicJet p = _ at he
  linear_combination he + cubicH ^ 3 * nativeCubicJet p * hc

theorem nativeRatioNumerator_gauge (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    cubicH ^ 4 * (nativeRatioNumerator p).derivative +
      4 * cubicH ^ 3 * nativeRatioNumerator p =
        cubicH * cubicB * cubicLift ((p - 1) / 2) (3 * ((p - 1) / 2)) (nativeJetField p).derivative := by
  have he := nativeCubicJet_gauge p hp
  simp only [nativeRatioNumerator, derivative_mul, cubicH_derivative]
  linear_combination cubicH * he

theorem nativeRatioNumerator_rational (p : ℕ) [Fact p.Prime] :
    algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeRatioNumerator p) =
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ (3 * ((p - 1) / 2) + 1) *
        (nativeJetField p).eval₂ RatFunc.C
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
            (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) := by
  rw [nativeRatioNumerator, map_mul, nativeCubicJet,
    cubicLift_rational_eval ((p - 1) / 2) (3 * ((p - 1) / 2))
      (nativeJetField p) (nativeJetField_degree p) (by omega), pow_succ]
  ring

theorem nativeField_cubic_ne_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeField p (p / 6)).eval₂ RatFunc.C
      (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) ≠ 0 := by
  have hY : actualGauss p ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
    simp [actualGauss_origin] at he
  have hY2 := RatFunc.algebraMap_ne_zero (pow_ne_zero 2 hY)
  have he := actual_cubic_rational_hasse p hp
  intro hf
  rw [hf, mul_zero] at he
  exact hY2 he.symm

/-- Exact quotient attachment of the actual full native numerator, with its genuine denominator. -/
theorem nativeRatioNumerator_quotient (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (nativeRatioNumerator p) /
      ((algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ p *
        algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (actualGauss p ^ 2)) =
      (nativeJetField p).eval₂ RatFunc.C
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) /
        (nativeField p (p / 6)).eval₂ RatFunc.C
          (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicA /
            (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) cubicH) ^ 3) := by
  have hH := RatFunc.algebraMap_ne_zero (cubicH_ne_zero (K := ZMod p))
  have hF := nativeField_cubic_ne_zero p hp
  have hn := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hN : 3 * ((p - 1) / 2) + 1 = p + (p - 1) / 2 := by omega
  rw [nativeRatioNumerator_rational, ← actual_cubic_rational_hasse p hp, hN, pow_add]
  field_simp

end WPActualNativeCubicJet
