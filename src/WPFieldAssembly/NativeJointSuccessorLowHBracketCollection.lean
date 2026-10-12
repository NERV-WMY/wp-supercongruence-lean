import WPFieldAssembly.NativeClosureLowHCollection
import WPFieldAssembly.NativeClosureLowHSource
import WPFieldAssembly.NativeClosureUniversalSource

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPActualChiSource
open WPFieldAssembly.ActualBpairContraction WPFieldAssembly.GreenLaurentOperators
open WPFieldAssembly.ActualBpairLowHLocalPole
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.NativeClosureLowH

variable {K : Type*} [Field K]
set_option maxHeartbeats 2200000

/-- The remaining bracket derivative has its original finite odd-log and
full Frobenius terms. This cleared identity precedes any reciprocal
pullback, signed-band extraction or origin evaluation. -/
theorem native_original_bracketT_cleared_derivative (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c : K) :
    (1 - X ^ 2 : K[X]) * (WPFiniteNC122Residue.bracketT p c).derivative =
      Polynomial.C (2 / 3 : K) * WPFiniteKSource.OP p -
        Polynomial.C (2 / 9 : K) * X * (WPFiniteKSource.LPsrc p - Polynomial.C c) +
      Polynomial.C (2 / 3 : K) * X ^ p *
        ((WPFiniteKSource.LPsrc p - Polynomial.C c) -
          Polynomial.C (WPFiniteNC122.q p - 2 * c / 3)) := by
  have hK := WPFiniteKSource.KsrcP_cleared_derivative (K := K) p hp c
  have hL := WPFiniteKSource.LPsrc_cleared_derivative (K := K) p hp
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h9 : (9 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 9
    (Finset.mem_Ico.mpr (by omega))
  have hc : (2 / 3 : K) * (2 / 3) - 2 / 3 + 2 / 9 = 0 := by
    field_simp [h3, h9]
    ring
  have hcP := congrArg (Polynomial.C : K → K[X]) hc
  simp only [map_add, map_sub, map_mul, map_zero] at hcP
  simp only [WPFiniteNC122Residue.bracketT, derivative_add, derivative_sub,
    derivative_mul, derivative_C, zero_mul, zero_add, add_zero,
    derivative_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]
  linear_combination (norm := (simp only [div_eq_mul_inv, map_mul, map_ofNat, map_neg, one_mul]; ring))
    -Polynomial.C (2 / 3 : K) * hK -
    Polynomial.C (2 / 3 : K) * (WPFiniteKSource.LPsrc p - Polynomial.C c) * hL +
    X * (WPFiniteKSource.LPsrc p - Polynomial.C c) * hcP

/-- Quadratic descent gives the actual bracket derivative before its
reciprocal cubic pullback. The complete odd-log quotient and the N band
remain explicit; no endpoint or negative half is omitted. -/
theorem native_original_bracketQ_cleared_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (c : ZMod p) :
    (X : (ZMod p)[X]) * (WPFiniteNC122Residue.bracketQ p c).derivative =
      -Polynomial.C (1 / 3 : ZMod p) *
        WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
          (WPFiniteKSource.OP p).divX +
      Polynomial.C (1 / 9 : ZMod p) *
        (ActualNormCrossAttachment.actualLogNative p - Polynomial.C c) -
      Polynomial.C (1 / 3 : ZMod p) * (1 - X) ^ ((p - 1) / 2) *
        ((ActualNormCrossAttachment.actualLogNative p - Polynomial.C c) -
          Polynomial.C (WPFiniteNC122.q p - 2 * c / 3)) := by
  have hO0 : (WPFiniteKSource.OP p : (ZMod p)[X]).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [WPFiniteKSource.OP, eval_mul, eval_sub, eval_comp,
      eval_neg, eval_X, neg_zero, sub_self, mul_zero]
  have hO : (WPFiniteKSource.OP p : (ZMod p)[X]).comp (-X) =
      -WPFiniteKSource.OP p := by
    simp only [WPFiniteKSource.OP, mul_comp, C_comp, sub_comp,
      comp_neg_X_comp_neg_X]
    ring
  have hdiv : (X : (ZMod p)[X]) * (WPFiniteKSource.OP p).divX =
      WPFiniteKSource.OP p := by
    simpa only [hO0, map_zero, add_zero] using
      X_mul_divX_add (WPFiniteKSource.OP (K := ZMod p) p)
  have hOdiv : ((WPFiniteKSource.OP p : (ZMod p)[X]).divX).comp (-X) =
      (WPFiniteKSource.OP p).divX := by
    have he := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hdiv
    simp only [mul_comp, X_comp, hO] at he
    apply mul_left_cancel₀ (neg_ne_zero.mpr (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
    linear_combination he + hdiv
  have hOc := ActualNormCrossAttachment.even_native_attachment p hp
    (WPFiniteKSource.OP p).divX hOdiv
  have hLc := ActualNormCrossAttachment.even_native_attachment p hp
    (WPFiniteKSource.LPsrc p) (WPFiniteNC122Residue.LPsrc_even p)
  change (ActualNormCrossAttachment.actualLogNative p).comp (1 - X ^ 2) =
    WPFiniteKSource.LPsrc p at hLc
  have hD : -2 * X * ((WPFiniteNC122Residue.bracketQ p c).derivative).comp
      (1 - X ^ 2) = (WPFiniteNC122Residue.bracketT p c).derivative := by
    have he := congrArg (fun P : (ZMod p)[X] => P.derivative)
      (WPFiniteNC122Residue.bracketQ_transport p hp c)
    rw [derivative_comp] at he
    simp only [derivative_sub, derivative_one, derivative_pow, derivative_X,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub, map_ofNat] at he
    convert he using 1
    ring
  have hN : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have hpow : ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).comp (1 - X ^ 2) =
      X ^ (p - 1) := by
    simp only [pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel]
    rw [← pow_mul, hN]
  have hxp : (X : (ZMod p)[X]) * X ^ (p - 1) = X ^ p := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hdeg : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by
    compute_degree
    norm_num
  apply WPFieldAssembly.ConicKernel.comp_injective_nonconstant
    (1 - X ^ 2) (by rw [hdeg]; norm_num)
  simp only [mul_comp, sub_comp, add_comp, neg_comp, C_comp, X_comp]
  rw [hOc, hLc, hpow]
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h2P : (2 : (ZMod p)[X]) ≠ 0 := Polynomial.C_ne_zero.mpr h2
  apply mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr h2P)
    (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
  have he := native_original_bracketT_cleared_derivative (K := ZMod p) p hp c
  linear_combination (norm := (simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]; ring))
    he + (1 - X ^ 2) * hD - Polynomial.C (2 / 3 : ZMod p) * hdiv -
    Polynomial.C (2 / 3 : ZMod p) *
      ((WPFiniteKSource.LPsrc p - Polynomial.C c) -
        Polynomial.C (WPFiniteNC122.q p - 2 * c / 3)) * hxp

/-- The complete reciprocal native carrier is the original reciprocal
cubic pullback of the actual finite log, with its harmonic constant fixed. -/
theorem native_v_original_log_pullback (p : ℕ) [Fact p.Prime] [CharP K p] :
    invert (actualAK (K := K) p).toLaurent =
      coefficientMap (ActualThreePhase.φ (K := K) p)
        (substituteOver (ActualNormCrossAttachment.actualLogNative p)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) -
      LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p) := by
  rw [actualAK, ← coefficientMap_toLaurent, ← coefficientMap_invert,
    ← ActualLowEuler.Qrev_eq_fieldV p,
    ← substituteOver_toLaurent (ActualNormCrossAttachment.actualLogMinusH p)
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]), substituteOver_invert]
  simp only [ActualNormCrossAttachment.actualLogMinusH, substituteOver,
    Polynomial.eval₂_sub, Polynomial.eval₂_C, map_sub, coefficientMap_C]
  rfl

/-- The actual finite logarithm keeps its complete half-Frobenius band
under quadratic descent, before any reciprocal source is substituted. -/
theorem native_original_log_quadratic_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    (2 : (ZMod p)[X]) * X *
        (ActualNormCrossAttachment.actualLogNative p).derivative =
      (1 - X) ^ ((p - 1) / 2) - 1 := by
  have hLc := ActualNormCrossAttachment.even_native_attachment p hp
    (WPFiniteKSource.LPsrc p) (WPFiniteNC122Residue.LPsrc_even p)
  change (ActualNormCrossAttachment.actualLogNative p).comp (1 - X ^ 2) =
    WPFiniteKSource.LPsrc p at hLc
  have hD : -2 * X * ((ActualNormCrossAttachment.actualLogNative p).derivative).comp
      (1 - X ^ 2) = (WPFiniteKSource.LPsrc p).derivative := by
    have he := congrArg (fun P : (ZMod p)[X] => P.derivative) hLc
    rw [derivative_comp] at he
    simp only [derivative_sub, derivative_one, derivative_pow, derivative_X,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_sub, map_ofNat] at he
    convert he using 1
    ring
  have hN : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have hpow : ((1 - X : (ZMod p)[X]) ^ ((p - 1) / 2)).comp (1 - X ^ 2) =
      X ^ (p - 1) := by
    simp only [pow_comp, sub_comp, one_comp, X_comp, sub_sub_cancel]
    rw [← pow_mul, hN]
  have hxp : (X : (ZMod p)[X]) * X ^ (p - 1) = X ^ p := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hdeg : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by
    compute_degree
    norm_num
  apply WPFieldAssembly.ConicKernel.comp_injective_nonconstant
    (1 - X ^ 2) (by rw [hdeg]; norm_num)
  simp only [mul_comp, sub_comp, ofNat_comp, one_comp, X_comp]
  rw [hpow]
  apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
  have he := WPFiniteKSource.LPsrc_cleared_derivative (K := ZMod p) p hp
  linear_combination -(1 - X ^ 2) * hD - he - hxp

/-- The original odd quotient has its complete finite source under
quadratic descent. This identity retains the last odd degree p-2 and the
same actual finite logarithm; it does not replace either by an infinite sum. -/
theorem native_original_odd_quotient_derivative (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) :
    2 * (1 - X : (ZMod p)[X]) *
        (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
          (WPFiniteKSource.OP p).divX).derivative -
      WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
        (WPFiniteKSource.OP p).divX =
      2 * (ActualNormCrossAttachment.actualLogNative p).derivative := by
  let O : (ZMod p)[X] := WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
    (WPFiniteKSource.OP p).divX
  have hO0 : (WPFiniteKSource.OP p : (ZMod p)[X]).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp only [WPFiniteKSource.OP, eval_mul, eval_sub, eval_comp,
      eval_neg, eval_X, neg_zero, sub_self, mul_zero]
  have hOdd : (WPFiniteKSource.OP p : (ZMod p)[X]).comp (-X) =
      -WPFiniteKSource.OP p := by
    simp only [WPFiniteKSource.OP, mul_comp, C_comp, sub_comp,
      comp_neg_X_comp_neg_X]
    ring
  have hdiv : (X : (ZMod p)[X]) * (WPFiniteKSource.OP p).divX =
      WPFiniteKSource.OP p := by
    simpa only [hO0, map_zero, add_zero] using
      X_mul_divX_add (WPFiniteKSource.OP (K := ZMod p) p)
  have hEven : ((WPFiniteKSource.OP p : (ZMod p)[X]).divX).comp (-X) =
      (WPFiniteKSource.OP p).divX := by
    have he := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hdiv
    simp only [mul_comp, X_comp, hOdd] at he
    apply mul_left_cancel₀ (neg_ne_zero.mpr (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
    linear_combination he + hdiv
  have hOc := ActualNormCrossAttachment.even_native_attachment p hp
    (WPFiniteKSource.OP p).divX hEven
  change O.comp (1 - X ^ 2) = (WPFiniteKSource.OP p).divX at hOc
  have hOR : (X : (ZMod p)[X]) * O.comp (1 - X ^ 2) =
      WPFiniteKSource.OP p := by rw [hOc]; exact hdiv
  have hD : (WPFiniteKSource.OP p : (ZMod p)[X]).derivative =
      O.comp (1 - X ^ 2) - 2 * X ^ 2 * O.derivative.comp (1 - X ^ 2) := by
    have he := congrArg (fun P : (ZMod p)[X] => P.derivative) hOR
    rw [derivative_mul, derivative_X, derivative_comp] at he
    simp only [derivative_sub, derivative_one, derivative_pow, derivative_X,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, zero_sub, map_ofNat] at he
    convert he.symm using 1
    ring
  have hN : 2 * ((p - 1) / 2) = p - 1 := by
    obtain ⟨n, hn⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    omega
  have hL := congrArg (fun P : (ZMod p)[X] => P.comp (1 - X ^ 2))
    (native_original_log_quadratic_derivative p hp)
  simp only [mul_comp, sub_comp, ofNat_comp, one_comp, X_comp,
    pow_comp, sub_sub_cancel] at hL
  rw [← pow_mul, hN] at hL
  have hdeg : (1 - X ^ 2 : (ZMod p)[X]).natDegree = 2 := by
    compute_degree
    norm_num
  have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdeg
    norm_num at hdeg
  apply WPFieldAssembly.ConicKernel.comp_injective_nonconstant
    (1 - X ^ 2) (by rw [hdeg]; norm_num)
  change (2 * (1 - X) * O.derivative - O).comp (1 - X ^ 2) = _
  simp only [sub_comp, mul_comp, ofNat_comp, one_comp, X_comp, sub_sub_cancel]
  apply mul_left_cancel₀ hq
  have hOP := WPFiniteCubicLog.OP_cleared_derivative (K := ZMod p) p hp
  linear_combination -hOP + (1 - X ^ 2) * hD - hL

/-- The original reciprocal cubic derivative is cleared without dividing
by either endpoint factor. Every Laurent exponent is retained. -/
theorem native_original_Q_log_derivative :
    (WPFiniteZSource.Abar : K[X]).toLaurent *
        D (WPFieldAssembly.NativeScalarRows.originalQ : K[T;T⁻¹]) =
      WPFieldAssembly.NativeScalarRows.originalQ * 3 * (4 * T (-1) - 11) := by
  have ht := ActualLowEuler.T_one_inverse (K := K)
  rw [ActualLowEuler.D_originalQ_factor,
    WPFieldAssembly.NativeScalarRows.originalQ_factor]
  simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_X]
  linear_combination
    (3 * LaurentPolynomial.C ((125 : K)⁻¹) * (4 * T (-1) - 1) *
      (4 * T (-1) - 11) * (-4 * T 1 * T (-1) - 4 + 17 * T (-1))) * ht

/-- Multiplication by the actual H pullback gives the original y*dlogQ
source, including its origin and all negative powers. -/
theorem native_original_Q_y_density (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent *
        D (WPFieldAssembly.NativeScalarRows.originalQ : K[T;T⁻¹]) =
      WPFieldAssembly.NativeScalarRows.originalQ * lowHLinearYQLog H := by
  rw [lowHBranchYQuotient_source H h0, map_mul, native_qlog_density H h0]
  linear_combination
    (lowHBranchYQuotient H).toLaurent * (native_original_Q_log_derivative (K := K))

/-- The half-Frobenius power of the complete reciprocal coordinate has
its original added-point phase in cleared form. Neither the added-point
factor nor a branch factor is divided out. -/
theorem native_original_Q_half_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (4 * T (-1) - 11 : K[T;T⁻¹]) *
        (1 - WPFieldAssembly.NativeScalarRows.originalQ) ^ ((p - 1) / 2) =
      T (-(((p - 1) / 2 : ℕ) : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (4 * T (-(p : ℤ)) - 11) := by
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hc : (125 : K[X]) * Polynomial.C ((125 : K)⁻¹) = 1 := by
    change Polynomial.C (125 : K) * Polynomial.C ((125 : K)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ h125, map_one]
  have hV : (WPFiniteLVSource.V : K[X]) = 1 - WPFiniteNC122Residue.VP := by
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr h125)
    change (125 : K[X]) * WPFiniteLVSource.V =
      125 * (1 - WPFiniteNC122Residue.VP)
    rw [WPFiniteLVSource.V_numerator p hp, WPFiniteNC122Residue.VP]
    linear_combination (4 - X) * (4 * X - 1) ^ 2 * hc
  have hVP : (WPFiniteNC122Residue.Qrev : K[X]) = WPFiniteNC122Residue.VP := by
    rw [WPFiniteNC122Residue.Qrev_factored, WPFiniteNC122Residue.VP]
    ring
  have hVi : invert (WPFiniteLVSource.V : K[X]).toLaurent =
      1 - (WPFieldAssembly.NativeScalarRows.originalQ : K[T;T⁻¹]) := by
    rw [hV, map_sub, map_one, map_sub, map_one, ← hVP,
      WPFieldAssembly.NativeScalarRows.originalQ]
  have hh := congrArg (fun P : K[X] => P.toLaurent)
    (WPFiniteLVSource.V_half_power (K := K) p hp)
  simp only [map_mul, map_sub, map_pow, map_ofNat,
    Polynomial.toLaurent_X] at hh
  have hi := congrArg invert hh
  rw [map_mul, map_mul, WPFiniteZSource.invert_squared_power] at hi
  simpa only [map_mul, map_sub, map_ofNat, invert_T, map_pow, hVi,
    T_pow, mul_neg, mul_one] using hi

/-- The complete half-Frobenius source is exactly the derivative of the
original reciprocal finite log. It is collected only after the cleared
cubic source and the nonzero complete coordinate have been proved. -/
theorem native_original_log_weighted_pullback (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (H : (ZMod p)[X]) (h0 : H.coeff 0 = 0) :
    (1 - (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) ^
        ((p - 1) / 2) * lowHLinearYQLog H =
      2 * ((lowHCubicY H).toLaurent *
        D (substituteOver (ActualNormCrossAttachment.actualLogNative p)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]))) +
      lowHLinearYQLog H := by
  let Q : (ZMod p)[T;T⁻¹] := WPFieldAssembly.NativeScalarRows.originalQ
  let F := (1 - Q) ^ ((p - 1) / 2)
  have he := congrArg (fun P : (ZMod p)[X] =>
    P.eval₂ (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) Q)
    (native_original_log_quadratic_derivative p hp)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_one] at he
  change 2 * Q * substituteOver
    (ActualNormCrossAttachment.actualLogNative p).derivative Q = F - 1 at he
  have hQ := native_original_Q_y_density (K := ZMod p) H h0
  have hn : Q ≠ 0 := ActualLowEuler.actual_originalQ_ne_zero p hp
  apply mul_left_cancel₀ hn
  rw [ActualLowEuler.D_substitute_originalQ]
  change Q * (F * lowHLinearYQLog H) = _
  linear_combination
    -(lowHCubicY H).toLaurent * D Q * he - (F - 1) * hQ

/-- The full bracket derivative now uses its genuine reciprocal log
derivative. The original odd-log quotient remains explicit for its conic
collection; no endpoint value or signed band is assigned. -/
theorem native_original_bracket_weighted_pullback (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (c : ZMod p) (H : (ZMod p)[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * D (substituteOver
        (WPFiniteNC122Residue.bracketQ p c)
        (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) =
      -LaurentPolynomial.C (1 / 3 : ZMod p) *
        substituteOver (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
          (WPFiniteKSource.OP p).divX)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) *
        lowHLinearYQLog H +
      LaurentPolynomial.C (1 / 9 : ZMod p) *
        (substituteOver (ActualNormCrossAttachment.actualLogNative p)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) -
          LaurentPolynomial.C c) * lowHLinearYQLog H -
      LaurentPolynomial.C (1 / 3 : ZMod p) *
        ((substituteOver (ActualNormCrossAttachment.actualLogNative p)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) -
          LaurentPolynomial.C c) -
          LaurentPolynomial.C (WPFiniteNC122.q p - 2 * c / 3)) *
        (2 * ((lowHCubicY H).toLaurent *
          D (substituteOver (ActualNormCrossAttachment.actualLogNative p)
            (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]))) +
          lowHLinearYQLog H) := by
  let Q : (ZMod p)[T;T⁻¹] := WPFieldAssembly.NativeScalarRows.originalQ
  let L := substituteOver (ActualNormCrossAttachment.actualLogNative p) Q -
    LaurentPolynomial.C c
  let O := substituteOver (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
    (WPFiniteKSource.OP p).divX) Q
  let a := LaurentPolynomial.C (WPFiniteNC122.q p - 2 * c / 3)
  let F := (1 - Q) ^ ((p - 1) / 2)
  have he := congrArg (fun P : (ZMod p)[X] =>
    P.eval₂ (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) Q)
    (native_original_bracketQ_cleared_derivative p hp c)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_neg,
    Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_pow, Polynomial.eval₂_one] at he
  change Q * substituteOver (WPFiniteNC122Residue.bracketQ p c).derivative Q =
    -LaurentPolynomial.C (1 / 3 : ZMod p) * O +
      LaurentPolynomial.C (1 / 9 : ZMod p) * L -
      LaurentPolynomial.C (1 / 3 : ZMod p) * F * (L - a) at he
  have hQ := native_original_Q_y_density (K := ZMod p) H h0
  have hL := native_original_log_weighted_pullback p hp H h0
  have hn : Q ≠ 0 := ActualLowEuler.actual_originalQ_ne_zero p hp
  apply mul_left_cancel₀ hn
  rw [ActualLowEuler.D_substitute_originalQ]
  change Q * ((lowHCubicY H).toLaurent *
    (substituteOver (WPFiniteNC122Residue.bracketQ p c).derivative Q * D Q)) =
    Q * (-LaurentPolynomial.C (1 / 3 : ZMod p) * O * lowHLinearYQLog H +
      LaurentPolynomial.C (1 / 9 : ZMod p) * L * lowHLinearYQLog H -
      LaurentPolynomial.C (1 / 3 : ZMod p) * (L - a) *
        (2 * ((lowHCubicY H).toLaurent *
          D (substituteOver (ActualNormCrossAttachment.actualLogNative p) Q)) +
          lowHLinearYQLog H))
  linear_combination
    (lowHCubicY H).toLaurent * D Q * he +
    (-LaurentPolynomial.C (1 / 3 : ZMod p) * O +
      LaurentPolynomial.C (1 / 9 : ZMod p) * L -
      LaurentPolynomial.C (1 / 3 : ZMod p) * F * (L - a)) * hQ -
    Q * LaurentPolynomial.C (1 / 3 : ZMod p) * (L - a) * hL

/-- The original odd quotient and log keep their same reciprocal cubic
differential. Its cleared weighted source is ready for the joint CM/H
branch collection and retains the complete reciprocal coordinate. -/
theorem native_original_odd_weighted_pullback (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (H : (ZMod p)[X]) (h0 : H.coeff 0 = 0) :
    2 * (1 - (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) *
        ((lowHCubicY H).toLaurent * D (substituteOver
          (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
            (WPFiniteKSource.OP p).divX)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]))) -
      WPFieldAssembly.NativeScalarRows.originalQ *
        substituteOver (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
          (WPFiniteKSource.OP p).divX)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]) *
        lowHLinearYQLog H =
      2 * ((lowHCubicY H).toLaurent *
        D (substituteOver (ActualNormCrossAttachment.actualLogNative p)
          (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹]))) := by
  let Q : (ZMod p)[T;T⁻¹] := WPFieldAssembly.NativeScalarRows.originalQ
  let O : (ZMod p)[X] := WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
    (WPFiniteKSource.OP p).divX
  have he := congrArg (fun P : (ZMod p)[X] =>
    P.eval₂ (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) Q)
    (native_original_odd_quotient_derivative p hp)
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_ofNat, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, Polynomial.eval₂_X] at he
  change 2 * (1 - Q) * substituteOver O.derivative Q - substituteOver O Q =
    2 * substituteOver (ActualNormCrossAttachment.actualLogNative p).derivative Q at he
  have hQ := native_original_Q_y_density (K := ZMod p) H h0
  simp only [ActualLowEuler.D_substitute_originalQ]
  linear_combination
    (lowHCubicY H).toLaurent * D Q * he + substituteOver O Q * hQ

/-- This is the actual Euler bracket source, with the genuine complete
reciprocal carrier v. Its original odd quotient is retained explicitly for
the joint conic collection, rather than assigned an independent value. -/
theorem native_actual_Euler_bracket_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    coefficientMap (ActualThreePhase.φ (K := K) p) (actualEulerBracketDensity p) =
      -LaurentPolynomial.C (1 / 3 : K) *
        coefficientMap (ActualThreePhase.φ (K := K) p)
          (substituteOver (WPFieldAssembly.NativeQuadraticInverse.quadraticInverse
            (WPFiniteKSource.OP p).divX)
            (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) *
        lowHLinearYQLog (nativeH (K := K) p) +
      LaurentPolynomial.C (1 / 9 : K) * invert (actualAK (K := K) p).toLaurent *
        lowHLinearYQLog (nativeH (K := K) p) -
      LaurentPolynomial.C (1 / 3 : K) *
        (invert (actualAK (K := K) p).toLaurent -
          LaurentPolynomial.C (ActualThreePhase.φ (K := K) p
            (WPFiniteNC122.q (K := ZMod p) p) - 2 * ActualGreenResidue.hK p / 3)) *
        (2 * ((lowHCubicY (nativeH (K := K) p)).toLaurent *
          D (invert (actualAK (K := K) p).toLaurent)) +
          lowHLinearYQLog (nativeH (K := K) p)) := by
  let f : ZMod p →+* K := ActualThreePhase.φ p
  let H : (ZMod p)[X] := ActualLowEuler.actualH p
  have h0 : H.coeff 0 = 0 := by
    simp [H, ActualLowEuler.actualH, ActualR0Node.unitEuler_coeff]
  have hVP : (WPFiniteNC122Residue.VP : (ZMod p)[X]).map f =
      (WPFiniteNC122Residue.VP : K[X]) := by
    simp only [WPFiniteNC122Residue.VP, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_ofNat, Polynomial.map_one, map_inv₀, map_ofNat]
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]).map f =
      (WPFiniteZSource.Abar : K[X]) := by
    simp only [WPFiniteZSource.Abar, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_ofNat, Polynomial.map_one]
  have hy : coefficientMap f (lowHCubicY H).toLaurent =
      (lowHCubicY (nativeH (K := K) p)).toLaurent := by
    rw [coefficientMap_toLaurent, lowHCubicY, Polynomial.map_comp, hVP]
    rfl
  have hQ : coefficientMap f (lowHBranchYQuotient H).toLaurent =
      (lowHBranchYQuotient (nativeH (K := K) p)).toLaurent := by
    have he := congrArg (coefficientMap f)
      (congrArg (fun P : (ZMod p)[X] => P.toLaurent)
        (lowHBranchYQuotient_source H h0))
    simp only [map_mul] at he
    rw [hy, coefficientMap_toLaurent, hA] at he
    apply mul_left_cancel₀ (WPFiniteZSource.Abar_nonzero (K := K) p hp)
    rw [← he, lowHBranchYQuotient_source _ (nativeH_origin p), map_mul]
  have hyl : coefficientMap f (lowHLinearYQLog H) =
      lowHLinearYQLog (nativeH (K := K) p) := by
    simp only [lowHLinearYQLog, lowHLinearYOverX, map_sub, map_mul, map_ofNat,
      Polynomial.toLaurent_X, coefficientMap_T, hy, hQ]
  have hh : f (WPFiniteNC122.h (K := ZMod p) p) =
      ActualGreenResidue.hK (K := K) p := by
    change f (WPFiniteNC122.h (K := ZMod p) p) =
      f (WPActualGaussBottom.fieldHarmonic p (p / 6))
    rw [actual_harmonic_is_finite_h p hp]
  have hL : coefficientMap f
      (substituteOver (ActualNormCrossAttachment.actualLogNative p)
        (WPFieldAssembly.NativeScalarRows.originalQ : (ZMod p)[T;T⁻¹])) =
      invert (actualAK (K := K) p).toLaurent +
        LaurentPolynomial.C (ActualGreenResidue.hK (K := K) p) := by
    have he := native_v_original_log_pullback (K := K) p
    linear_combination -he
  have he := native_original_bracket_weighted_pullback p hp
    (WPFiniteNC122.h (K := ZMod p) p) H h0
  have hm := congrArg (coefficientMap f) he
  simp only [map_mul, map_add, map_sub, map_neg, coefficientMap_C,
    D_coefficientMap, map_div₀, map_one, map_ofNat, hy, hyl, hL, hh] at hm
  simp only [D_C, add_zero, add_sub_cancel_right] at hm
  rw [actual_EulerBracket_source p, ← nativeH_original_Hpull p hp]
  simpa only [map_sub, actualBracketQK, f] using hm

end WPFieldAssembly.NativeClosureLowH
