import WPFieldAssembly.GreenLaurentOperators
import WPFieldAssembly.ActualR0Node
import WPActualNativeRemainderProjection
import WPFiniteJWeightedResidue
import WPFiniteFifthSourceContraction
import WPActualPositiveResidueCarry

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.NativeScalarRows

variable {K : Type*} [Field K]

/-- The actual reciprocal cubic coordinate, with all negative powers. -/
noncomputable def originalQ : K[T;T⁻¹] :=
  invert (WPFiniteNC122Residue.Qrev : K[X]).toLaurent

noncomputable def Fnegative : K[T;T⁻¹] :=
  invert (WPFiniteNC122Residue.Frev : K[X]).toLaurent

noncomputable def reciprocalDensity (G : K[X]) : K[T;T⁻¹] :=
  invert (WPFiniteNC122Residue.canceledDensity G).toLaurent

theorem originalQ_factor :
    (originalQ : K[T;T⁻¹]) =
      LaurentPolynomial.C ((125 : K)⁻¹) * (4 * T (-1) - 1) ^ 2 *
        (4 - T (-1)) := by
  rw [originalQ, WPFiniteNC122Residue.Qrev_factored]
  simp only [_root_.map_mul, _root_.map_pow, _root_.map_sub, _root_.map_ofNat, _root_.map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    invert_C, invert_T]

theorem Fnegative_factor :
    (Fnegative : K[T;T⁻¹]) =
      LaurentPolynomial.C ((125 : K)⁻¹) * 3 * T (-1) *
        (4 * T (-1) - 1) * (11 * T (-1) - 4) := by
  have hf : (WPFiniteNC122Residue.Frev : K[X]) =
      Polynomial.C ((125 : K)⁻¹) * 3 * X *
        (4 * X - 1) * (11 * X - 4) := by
    unfold WPFiniteNC122Residue.Frev
    simp only [div_eq_mul_inv, _root_.map_mul, _root_.map_ofNat]
    ring
  rw [Fnegative, hf]
  simp only [_root_.map_mul, _root_.map_sub, _root_.map_ofNat, _root_.map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    invert_C, invert_T]

/-- This identity cancels both original endpoint factors algebraically. -/
theorem original_cubic_density_cleared :
    (WPFiniteZSource.Abar : K[X]).toLaurent * Fnegative =
      originalQ * (33 - 12 * T 1) := by
  have htx : (T 1 : K[T;T⁻¹]) * T (-1) = 1 := by
    rw [← T_add]
    norm_num
  have hxt : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by
    simpa only [mul_comm] using htx
  have hfirst : (4 - T 1 : K[T;T⁻¹]) =
      (4 * T (-1) - 1) * T 1 := by
    calc
      _ = 4 * (T (-1) * T 1) - T 1 := by rw [hxt, mul_one]
      _ = _ := by ring
  have hsecond : (4 * T 1 - 1 : K[T;T⁻¹]) =
      (4 - T (-1)) * T 1 := by
    calc
      _ = 4 * T 1 - T (-1) * T 1 := by rw [hxt]
      _ = _ := by ring
  have hlinear : (3 * T 1 * (11 * T (-1) - 4) :
      K[T;T⁻¹]) = 33 - 12 * T 1 := by
    calc
      _ = 33 * (T 1 * T (-1)) - 12 * T 1 := by ring
      _ = _ := by rw [htx]; ring
  simp only [WPFiniteZSource.Abar, _root_.map_mul, _root_.map_sub,
    _root_.map_ofNat, _root_.map_one, Polynomial.toLaurent_X]
  rw [hfirst, hsecond, Fnegative_factor, originalQ_factor]
  calc
    _ = LaurentPolynomial.C ((125 : K)⁻¹) * (4 * T (-1) - 1) ^ 2 *
        (4 - T (-1)) *
        (3 * T 1 * (11 * T (-1) - 4)) *
        (T 1 * T (-1)) := by ring
    _ = _ := by rw [hlinear, htx, mul_one]

theorem ev_originalQ (a : K) (ha : a ≠ 0) :
    ev a ha (originalQ : K[T;T⁻¹]) =
      (WPFiniteNC122Residue.Qrev : K[X]).eval a⁻¹ := by
  rw [ev, originalQ, WPFiniteJWeightedResidue.inversion_eval,
    LaurentPolynomial.eval₂_toLaurent]
  simp only [Polynomial.eval₂_id, Units.val_inv_eq_inv_val,
    Units.val_mk0]

theorem ev_substituteOver (G : K[X]) (L : K[T;T⁻¹])
    (a : K) (ha : a ≠ 0) :
    ev a ha (substituteOver G L) = G.eval (ev a ha L) := by
  induction G using Polynomial.induction_on' with
  | add G H hG hH =>
      simp only [substituteOver, Polynomial.eval₂_add,
        _root_.map_add, Polynomial.eval_add]
      exact congrArg₂ (· + ·) hG hH
  | monomial n c =>
      simp [substituteOver, ev, LaurentPolynomial.eval₂_C,
        Polynomial.eval₂_monomial]

theorem reciprocalDensity_factor (G : K[X]) :
    reciprocalDensity G =
      substituteOver G.divX originalQ * Fnegative := by
  unfold reciprocalDensity WPFiniteNC122Residue.canceledDensity
  simp only [_root_.map_mul]
  rw [← substituteOver_toLaurent G.divX
    (WPFiniteNC122Residue.Qrev : K[X]),
    substituteOver_invert]
  rfl

/-- Whole original Laurent cancellation; no equality of sampled values is used. -/
theorem actual_original_whole_cancellation
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (G : K[X]) (hG : G.eval 0 = 0) :
    weightedDD (substituteOver G originalQ) =
      reciprocalDensity G := by
  have h4 : (4 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
  have ha : ev (1 / 4 : K) (div_ne_zero one_ne_zero h4)
      (originalQ : K[T;T⁻¹]) = 0 := by
    rw [ev_originalQ]
    have hi : (1 / 4 : K)⁻¹ = 4 := by simp
    rw [hi, WPFiniteNC122Residue.Qrev_factored]
    simp
  have hb : ev (4 : K) h4 (originalQ : K[T;T⁻¹]) = 0 := by
    rw [ev_originalQ, WPFiniteNC122Residue.Qrev_factored]
    simp [mul_inv_cancel₀ h4]
  have hga : ev (1 / 4 : K) (div_ne_zero one_ne_zero h4)
      (substituteOver G originalQ) = 0 := by
    rw [ev_substituteOver, ha, hG]
  have hgb : ev (4 : K) h4
      (substituteOver G originalQ) = 0 := by
    rw [ev_substituteOver, hb, hG]
  have hg0 : G.coeff 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero] using hG
  have hd : X * G.divX = G := by
    simpa only [hg0, _root_.map_zero, add_zero] using X_mul_divX_add G
  have hs : originalQ * substituteOver G.divX originalQ =
      substituteOver G originalQ := by
    have hh := congrArg
      (Polynomial.eval₂RingHom LaurentPolynomial.C
        (originalQ : K[T;T⁻¹])) hd
    simpa only [substituteOver, Polynomial.coe_eval₂RingHom,
      _root_.map_mul, Polynomial.eval₂_X] using hh
  have hc := weightedDD_cleared h4
    (substituteOver G (originalQ : K[T;T⁻¹]))
  rw [hga, hgb] at hc
  simp only [_root_.map_zero, mul_zero, add_zero] at hc
  apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero p hp)
  calc
    _ = substituteOver G originalQ * (33 - 12 * T 1) := hc
    _ = (WPFiniteZSource.Abar : K[X]).toLaurent *
        reciprocalDensity G := by
      rw [reciprocalDensity_factor]
      calc
        _ = substituteOver G.divX originalQ *
            (originalQ * (33 - 12 * T 1)) := by
              rw [← hs]
              ring
        _ = _ := by
          rw [← original_cubic_density_cleared]
          ring

/-- Original unweighted origin residue, with both endpoint cancellations proved. -/
theorem actual_original_origin_residue
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (G : K[X]) (hG : G.eval 0 = 0) :
    (weightedDD (substituteOver G originalQ)).coeff (-1) =
      (WPFiniteNC122Residue.canceledDensity G).coeff 1 := by
  rw [actual_original_whole_cancellation p hp G hG,
    reciprocalDensity, LaurentPolynomial.invert_apply,
    show -(-1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
    WPFiniteJCarrier.toLaurent_coeff_nat]

/-- The actual integral reciprocal cubic is formed before either coefficient map. -/
noncomputable def originalQIntegral
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPPIntegralReduction.integralRationals p)[T;T⁻¹] :=
  invert (WPHasseIntegralTransport.integralV p (by omega)).toLaurent

theorem originalQIntegral_value
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (WPPIntegralReduction.integralRationals p).subtype
      (originalQIntegral p hp) = WPActualEtaPole.Qx := by
  rw [originalQIntegral, coefficientMap_invert,
    coefficientMap_toLaurent,
    WPHasseIntegralTransport.integralV_map_rational]
  change invert WPActualEtaPole.Vx = WPActualEtaPole.Qx
  exact WPActualChiSource.actual_Vx_reciprocal

theorem originalQIntegral_field
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (WPPIntegralReduction.residueHom p)
      (originalQIntegral p hp) =
        (originalQ : (ZMod p)[T;T⁻¹]) := by
  rw [originalQIntegral, coefficientMap_invert,
    coefficientMap_toLaurent,
    WPHasseIntegralTransport.integralV_map_field, originalQ]
  have h125 : ((1 / 125 : ℚ) : ZMod p) =
      (1 / 125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Rat.cast_inv_nat (α := ZMod p) 125)
  congr 1
  congr 1
  rw [WPHasseIntegralTransport.fieldV, h125,
    WPFiniteNC122Residue.Qrev_factored]
  simp only [div_eq_mul_inv, one_mul]

noncomputable def actualGKQ
    (p : ℕ) [Fact p.Prime] [CharP K p] : K :=
  (weightedDD (substituteOver
    (WPFiniteNC122Residue.bracketQ p (WPFiniteNC122.h p))
      originalQ)).coeff (-1)

theorem actual_GKQ_original_attachment
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    actualGKQ (K := K) p =
      (WPFiniteNC122Residue.canceledDensity
        (WPFiniteNC122Residue.bracketQ p
          (WPFiniteNC122.h p))).coeff 1 := by
  exact actual_original_origin_residue p hp _
    (WPFiniteNC122Residue.bracketQ_zero_end p hp _)

/-- Correct NC130 scalar, attached to the original Laurent residue. -/
theorem actual_GKQ_corrected_value
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    actualGKQ p =
      2 * WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u) -
      4 * WPFiniteNC122.a0 p u ^ 2 / 3 +
      2 * (WPFiniteNC122.q p - WPFiniteNC122.h p) *
        WPFiniteNC122.a0 p u -
      2 * WPFiniteNC122.h p ^ 2 / 3 +
      2 * WPFiniteNC122.q p * WPFiniteNC122.h p -
      WPFiniteNC122.q p ^ 2 +
      22 * WPFiniteNC122.h0J p u / 15 := by
  rw [actual_GKQ_original_attachment p hp]
  exact WPFiniteNC122Residue.actual_NC122_corrected_value
    p hp u hu

/-- Whole original Frobenius-weight cancellation for the actual finite J carrier. -/
theorem actual_original_J_cleared
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : K[X]).toLaurent ^ p *
      WPFiniteJWeightedResidue.canceledJ p =
    LaurentPolynomial.C (3 : K) * T (p : ℤ) *
      (LaurentPolynomial.C (4 : K) * T 1 - LaurentPolynomial.C (11 : K)) ^ p *
        WPFiniteJCarrier.GJ p := by
  have h3 : (3 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 3
      (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h45 : (45 : K) ≠ 0 := by
    rw [show (45 : K) = 3 ^ 2 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have hf (n : ℕ) :
      (LaurentPolynomial.C (n : K) : K[T;T⁻¹]) ^ p = LaurentPolynomial.C (n : K) := by
    rw [← _root_.map_pow, WPFiniteField.natCast_pow_char p n]
  have hb :
      (LaurentPolynomial.C (4 : K) * T 1 - LaurentPolynomial.C (11 : K) : K[T;T⁻¹]) ^ p =
        LaurentPolynomial.C (4 : K) * T (p : ℤ) - LaurentPolynomial.C (11 : K) := by
    have h4L : LaurentPolynomial.C (4 : K) ^ p =
        (LaurentPolynomial.C (4 : K) : K[T;T⁻¹]) := by
      simpa only [Nat.cast_ofNat] using hf 4
    have h11L : LaurentPolynomial.C (11 : K) ^ p =
        (LaurentPolynomial.C (11 : K) : K[T;T⁻¹]) := by
      simpa only [Nat.cast_ofNat] using hf 11
    have hs := congrArg (fun P : K[X] => P.toLaurent)
      (sub_pow_char (p := p) (Polynomial.C (4 : K) * X) (Polynomial.C (11 : K)))
    simp only [_root_.map_pow, _root_.map_sub, _root_.map_mul,
      Polynomial.toLaurent_C, Polynomial.toLaurent_X] at hs
    rw [hs, mul_pow, h4L, h11L, T_pow]
    simp
  have hc : (LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 45 : K) :
      K[T;T⁻¹]) = LaurentPolynomial.C (1 / 15 : K) := by
    rw [← _root_.map_mul]
    congr 1
    field_simp [h15, h45]
    ring
  rw [hb, WPFiniteZSource.GJ_phase,
    WPFiniteZSource.phase_factorization p hp,
    WPFiniteJWeightedResidue.canceledJ]
  calc
    _ = LaurentPolynomial.C (1 / 15 : K) * T (p : ℤ) *
        WPFiniteZSource.phase p *
        (LaurentPolynomial.C (4 : K) * T (p : ℤ) - LaurentPolynomial.C (11 : K)) *
        ((WPFiniteJSource.HJP p).toLaurent +
          invert (WPFiniteJSource.HJP p).toLaurent) := by ring
    _ = LaurentPolynomial.C (3 : K) * LaurentPolynomial.C (1 / 45 : K) * T (p : ℤ) *
        WPFiniteZSource.phase p *
        (LaurentPolynomial.C (4 : K) * T (p : ℤ) - LaurentPolynomial.C (11 : K)) *
        ((WPFiniteJSource.HJP p).toLaurent +
          invert (WPFiniteJSource.HJP p).toLaurent) := by rw [hc]
    _ = _ := by ring

/-- The full J functional retains its invisible 2p slot and both strict tails. -/
theorem actual_original_KJ_full_row
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    actualGKQ p +
      (2 : K) * WPFiniteJWeightedResidue.infinityQ
        (WPFiniteJWeightedResidue.canceledJ p) / 3 -
      207 * (WPFiniteJCarrier.GJ p : K[T;T⁻¹]).coeff
        (2 * (p : ℤ)) / 4 =
      2 * WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u) -
      4 * (11 * WPFifthEntropy.C p u / 5 -
        WPFiniteNC122.q p / 5 +
        3 * (WPFiniteJNormalization.r p +
          WPFiniteFifthSourceContraction.k p) / 2) ^ 2 / 3 +
      2 * (WPFiniteNC122.q p - WPFiniteNC122.h p) *
        (11 * WPFifthEntropy.C p u / 5 -
          WPFiniteNC122.q p / 5 +
          3 * (WPFiniteJNormalization.r p +
            WPFiniteFifthSourceContraction.k p) / 2) -
      2 * WPFiniteNC122.h p ^ 2 / 3 +
      2 * WPFiniteNC122.q p * WPFiniteNC122.h p -
      WPFiniteNC122.q p ^ 2 +
      77 * WPFiniteJNormalization.U_J p u / 75 +
      16 * (WPFiniteFifthSourceContraction.strictHigh p :
        K[X]).eval (1 / 4) / 45 +
      8 * (WPFiniteFifthSourceContraction.strictHigh p :
        K[X]).eval 4 / 45 := by
  calc
    _ =
        (WPFiniteNC122Residue.canceledDensity
          (WPFiniteNC122Residue.bracketQ p
            (WPFiniteNC122.h p))).coeff 1 +
        ((2 : K) * WPFiniteJWeightedResidue.infinityQ
            (WPFiniteJWeightedResidue.canceledJ p) / 3 -
          207 * (WPFiniteJCarrier.GJ p : K[T;T⁻¹]).coeff
            (2 * (p : ℤ)) / 4) := by
              rw [actual_GKQ_original_attachment p hp]
              ring
    _ =
        (WPFiniteNC122Residue.canceledDensity
          (WPFiniteNC122Residue.bracketQ p
            (WPFiniteNC122.h p))).coeff 1 +
        WPFiniteFifthSourceContraction.JfullFunctional p := by
              rw [WPFiniteJWeightedResidue.actual_full_J_functional p hp]
    _ = _ :=
      WPFiniteFifthSourceContraction.original_KJ_full_attachment
        p hp u hu

open WPPIntegralReduction
  WPFieldAssembly.ActualR0Node
  WPFieldAssembly.NativeOriginalResidues
  WPActualNativeCanonicalPart
  WPActualCanonicalFinitePart
  WPCartierPoleProjection

noncomputable def nativeBpair
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : ZMod p :=
  (29 / 6 : ZMod p) * valueAt p (nativeRemainder p hp) (1 / 4) -
    (23 / 6 : ZMod p) * valueAt p (nativeRemainder p hp) 4 +
    2 * (-2 * negativeValue p (nativeRemainder p hp) (1 / 4) -
      negativeValue p (nativeRemainder p hp) 4)

noncomputable def nativeCp
    (p : ℕ) [Fact p.Prime] : ZMod p :=
  (pullbackPolynomial p (nativeHJet p)).coeff p

theorem actual_native_C0
    (p : ℕ) [Fact p.Prime] :
    (pullbackPolynomial p (nativeHJet p)).coeff 0 =
      (nativeHJet p).eval (4 / 125 : ZMod p) := by
  rw [coeff_zero_eq_eval_zero, pullbackPolynomial, eval_comp]
  congr 1
  have h125 : ((1 / 125 : ℚ) : ZMod p) =
      (1 / 125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Rat.cast_inv_nat (α := ZMod p) 125)
  unfold WPHasseIntegralTransport.fieldV
  simp only [eval_mul, eval_C, eval_pow, eval_sub,
    eval_ofNat, eval_X, eval_one, mul_zero, zero_sub, h125]
  ring

theorem actual_native_period_scalar
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (625 / 216 : ZMod p) *
      (WPActualEtaIntegration.canonicalPeriod p
        ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      nativeBpair p hp -
        (nativeHJet p).eval (4 / 125 : ZMod p) / 6 +
        (113 / 336 : ZMod p) * nativeCp p := by
  have h :=
    WPActualNativeRemainderProjection.actual_native_normalized_period p hp
  rw [actual_native_C0 p] at h
  simpa only [nativeBpair, nativeCp] using h

theorem actual_rho_negative_original_norm
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (WPFirstResidue.integralActualRho p hp) +
      (5 / 4 : ZMod p) * residueHom p
        (WPMomentPrecision.NativeSecondLift.integralNegativeDigit p hp) =
      2 * residueHom p (integralDeltaUDigit p hp) -
        (nativeHJet p).eval (4 / 125 : ZMod p) / 6 -
        (originalNorm p : ZMod p) := by
  have h2 := WPActualGaussProper.small_cast_ne_zero
    p 2 (by norm_num) (by omega)
  have h4 := WPActualGaussProper.small_cast_ne_zero
    p 4 (by norm_num) (by omega)
  have h6 := WPActualGaussProper.small_cast_ne_zero
    p 6 (by norm_num) (by omega)
  have h12 := WPActualGaussProper.small_cast_ne_zero
    p 12 (by norm_num) (by omega)
  norm_num only [Nat.cast_ofNat] at h2 h4 h6 h12
  rw [actual_rho_norm_source p hp,
    integralNegativeDigit_norm_source p hp,
    original_norm_field p hp]
  field_simp [h2, h4, h6, h12]
  ring

/-- Exact actual joint scalar before the separately retained positive Cp carry. -/
theorem actual_joint_native_scalar_row
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (WPFirstResidue.integralActualRho p hp) +
      (5 / 4 : ZMod p) * residueHom p
        (WPMomentPrecision.NativeSecondLift.integralNegativeDigit p hp) -
      (625 / 216 : ZMod p) *
        (WPActualEtaIntegration.canonicalPeriod p
          ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      2 * residueHom p (integralDeltaUDigit p hp) -
        (originalNorm p : ZMod p) - nativeBpair p hp -
        (113 / 336 : ZMod p) * nativeCp p := by
  rw [actual_rho_negative_original_norm p hp,
    actual_native_period_scalar p hp]
  ring

/-- The actual positive digit cancels precisely the retained Cp period slot. -/
theorem actual_joint_native_scalar_with_positive
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    2 * residueHom p (WPFirstResidue.integralActualRho p hp) +
      (5 / 4 : ZMod p) * residueHom p
        (WPMomentPrecision.NativeSecondLift.integralNegativeDigit p hp) +
      (113 / 28 : ZMod p) * residueHom p
        (WPActualPositiveResidueCarry.integralPositiveDigit p hp 1 (by norm_num)) -
      (625 / 216 : ZMod p) *
        (WPActualEtaIntegration.canonicalPeriod p
          ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      2 * residueHom p (integralDeltaUDigit p hp) -
        (originalNorm p : ZMod p) - nativeBpair p hp := by
  have hrow := actual_joint_native_scalar_row p hp
  have hpos := (WPActualPositiveResidueCarry.actual_positive_residue_digits p hp).1
  change residueHom p
    (WPActualPositiveResidueCarry.integralPositiveDigit p hp 1 (by norm_num)) =
      nativeCp p / 12 at hpos
  have hcancel : (113 / 28 : ZMod p) * residueHom p
      (WPActualPositiveResidueCarry.integralPositiveDigit p hp 1 (by norm_num)) =
      (113 / 336 : ZMod p) * nativeCp p := by
    rw [hpos, show (336 : ZMod p) = 28 * 12 by norm_num]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  linear_combination hrow + hcancel

end WPFieldAssembly.NativeScalarRows
