import WPActualNativeQuadraticSquare
import WPActualRankTwoComparison
import WPActualNativeFirstIntegral
import WPFiniteWSource
import WPFiniteLVSource

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeFirstIntegral WPActualNativeJetRecurrence
  WPActualNativeJetODE
  WPActualNativeQuadraticSquare WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualRankTwoComparison WPActualRankTwoResidueSource WPActualGaussProper
  WPHasseIntegralTransport WPFiniteLVSource WPFiniteJHighCoefficient WPFiniteCubicLog
  WPFiniteKSource

namespace WPActualNativeJacobiJet

set_option maxHeartbeats 800000

/-- The entire original native jet under q=1-T^2; no coefficient is projected away. -/
noncomputable def nativeJacobiJet (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  (nativeJetField p).comp (1 - X ^ 2)

/-- Polynomial Bezout removes every proper pole before classifying the derivative kernel. -/
theorem proper_square_division {K : Type*} [Field K] (a : K) (ha : 2 * a = 1)
    (q Y n M : K[X]) (hY : Y ≠ 0)
    (hW : q * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2)
    (hM : M.derivative * Y - 2 * M * Y.derivative = 0) :
    ∃ k : K[X], M = Y ^ 2 * k ∧ k.derivative = 0 := by
  have haP : (2 : K[X]) * C a = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg (C : K → K[X]) ha
  let b := M * (Y + q * n.derivative) - C a * q * M.derivative * n
  have hb : M = Y * b := by
    dsimp only [b]
    linear_combination -M * hW + C a * q * n * hM + q * M * Y.derivative * n * haP
  have hbs : Y * b.derivative - Y.derivative * b = 0 := by
    have hh : Y * (Y * b.derivative - Y.derivative * b) = 0 := by
      rw [hb] at hM
      simp only [derivative_mul] at hM
      linear_combination hM
    exact (mul_eq_zero.mp hh).resolve_left hY
  let k := b * (Y + q * n.derivative) - q * b.derivative * n
  have hk : b = Y * k := by
    dsimp only [k]
    linear_combination -b * hW + q * n * hbs
  have hf : M = Y ^ 2 * k := by rw [hb, hk]; ring
  refine ⟨k, hf, ?_⟩
  have hh : Y ^ 3 * k.derivative = 0 := by
    rw [hf] at hM
    simp only [derivative_mul, derivative_sq, C_ofNat] at hM
    linear_combination hM
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 3 hY)

theorem nativeJacobiJet_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (nativeJacobiJet p).natDegree ≤ p - 1 := by
  have hq : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
  have hd := (natDegree_comp_le (p := nativeJetField p) (q := 1 - X ^ 2)).trans
    (Nat.mul_le_mul (WPActualNativeJetODE.nativeJetField_degree p) hq)
  have hn := WPFiniteWSource.half_exponent p hp
  unfold nativeJacobiJet
  omega

/-- Whole original native first integral after the exact quadratic coordinate change. -/
theorem nativeJacobiJet_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (actualLegendreJacobi p ^ 2 * (nativeJacobiJet p).derivative -
      (actualLegendreJacobi p ^ 2).derivative * nativeJacobiJet p) =
      -2 * X * actualLegendreJacobi p ^ 2 *
        (X ^ (p - 1) - actualLegendreJacobi p ^ 2) := by
  let q : (ZMod p)[X] := 1 - X ^ 2
  have he := congrArg (fun P : (ZMod p)[X] => P.comp q) (actual_native_first_integral p hp)
  simp only [mul_comp, sub_comp, pow_comp, X_comp, one_comp] at he
  rw [show (nativeField p (p / 6)).comp q = actualLegendreJacobi p ^ 2 from
    actual_native_Jacobi_square p hp] at he
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := by
    have := WPFiniteWSource.half_exponent p hp
    omega
  have hpw : (1 - q) ^ ((p - 1) / 2) = (X : (ZMod p)[X]) ^ (p - 1) := by
    dsimp only [q]
    rw [show (1 - (1 - X ^ 2) : (ZMod p)[X]) = X ^ 2 by ring, ← pow_mul, hhalf]
  rw [hpw] at he
  have hf := congrArg Polynomial.derivative (actual_native_Jacobi_square p hp)
  change ((nativeField p (p / 6)).comp q).derivative = (actualLegendreJacobi p ^ 2).derivative at hf
  simp only [derivative_comp] at hf
  have hdq : q.derivative = -2 * X := by simp [q, derivative_pow_succ]; ring
  rw [hdq] at hf
  have hDJ : (nativeJacobiJet p).derivative =
      (nativeJetField p).derivative.comp q * (-2 * X) := by
    unfold nativeJacobiJet
    rw [derivative_comp, hdq]
    ring
  rw [hDJ]
  unfold nativeJacobiJet
  linear_combination -2 * X * he + (nativeJetField p).comp q * q * hf

/-- The complete normalized rank-two first integral retains its T^p term. -/
theorem rankHatField_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (1 - X ^ 2) * (actualLegendreJacobi p * (rankHatField p).derivative -
      (actualLegendreJacobi p).derivative * rankHatField p) =
      X * actualLegendreJacobi p ^ 2 - X ^ p := by
  have hz : ((X : (ZMod p)[X]) ^ p).derivative = 0 := by simp [derivative_X_pow]
  simp only [rankHatField, derivative_sub, derivative_mul, derivative_add, derivative_C,
    add_zero, hz, zero_mul, zero_add]
  linear_combination actualLegendreJacobi p ^ 2 * evenLogPolynomial_source p hp -
    X ^ p * properLegendreJacobi_wronskian p (by omega)

theorem actualLegendreJacobi_nonzero (p : ℕ) [Fact p.Prime] : actualLegendreJacobi p ≠ 0 := by
  intro hz
  have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hz
  rw [actualLegendreJacobi_endpoint_one, eval_zero] at he
  exact one_ne_zero he

theorem derivative_zero_endpoint_one (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (hdeg : P.natDegree < p) (hD : P.derivative = 0) (h1 : P.eval 1 = 0) : P = 0 := by
  have hc : P - C (P.eval 0) = 0 := by
    apply finite_derivative_zero p
    · exact (natDegree_sub_le_of_le (Nat.le_refl _) (show (C (P.eval 0)).natDegree ≤ 0 by simp)).trans_lt
        (by simpa using hdeg)
    · simp
    · simp [hD]
  have hp0 : P = C (P.eval 0) := sub_eq_zero.mp hc
  have he := congrArg (fun Q : (ZMod p)[X] => Q.eval 1) hp0
  rw [h1, eval_C] at he
  rw [hp0, ← he, C_0]

/-- Genuine native jet equals the actual Q-divided rank-two polynomial, with every cutoff term. -/
theorem actual_native_Jacobi_jet (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeJacobiJet p = 2 * actualLegendreJacobi p * actualRankDividedField p (by omega) := by
  let Y := actualLegendreJacobi p
  let R := rankHatField p
  let M := nativeJacobiJet p - 2 * Y * R
  have hY : Y ≠ 0 := actualLegendreJacobi_nonzero p
  have hsource : M.derivative * Y - 2 * M * Y.derivative = 0 := by
    have he : (1 - X ^ 2) * Y * (M.derivative * Y - 2 * M * Y.derivative) = 0 := by
      have hn := nativeJacobiJet_wronskian p hp
      have hr := rankHatField_wronskian p hp
      dsimp only [M, Y, R]
      simp only [derivative_sub, derivative_mul, derivative_ofNat, zero_mul, zero_add]
      have hpower : (X : (ZMod p)[X]) ^ p = X * X ^ (p - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p)]
      rw [hpower] at hr
      simp only [derivative_sq, C_ofNat] at hn
      linear_combination hn - 2 * actualLegendreJacobi p ^ 2 * hr
    have hq : (1 - X ^ 2 : (ZMod p)[X]) ≠ 0 := by
      intro hz
      have hh := congrArg (fun P : (ZMod p)[X] => P.eval 0) hz
      norm_num at hh
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hq hY)
  obtain ⟨k, hk, hD⟩ := proper_square_division (1 / 2 : ZMod p)
    (field_half_identity p (by omega)) (1 - X ^ 2) Y (properLegendreJacobi p) M hY
    (properLegendreJacobi_wronskian p (by omega)) hsource
  have hdeg : M.natDegree < p := by
    have hd := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (2 : (ZMod p)[X]).natDegree ≤ 0 by simp)
        (actualLegendreJacobi_degree p)) (rankHatField_degree p hp)
    have hm := natDegree_sub_le_of_le (nativeJacobiJet_degree p hp) hd
    change M.natDegree ≤ max (p - 1) (0 + p / 6 + (p - 1 - p / 6)) at hm
    omega
  have hkdeg : k.natDegree < p := by
    by_cases hz : k = 0
    · subst k; simp; omega
    · rw [hk, natDegree_mul (pow_ne_zero 2 hY) hz] at hdeg
      omega
  have h1 : k.eval 1 = 0 := by
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hk
    simp only [M, Y, R, eval_sub, eval_mul, eval_ofNat, nativeJacobiJet,
      eval_comp, eval_sub, eval_one, eval_pow, eval_X, one_pow, sub_self,
      WPActualNativeJetODE.nativeJetField_origin, actualLegendreJacobi_endpoint_one,
      rankHatField_endpoint_one p hp, mul_zero, eval_pow, one_mul] at he
    exact he.symm
  have hz := derivative_zero_endpoint_one p k hkdeg hD h1
  have hm0 : M = 0 := by rw [hk, hz, mul_zero]
  have hm := sub_eq_zero.mp hm0
  rw [actual_rankDividedField_eq_hat p hp]
  exact hm

/-- Actual full native source, with the proper quotient and original finite logarithm cleared. -/
theorem actual_native_Jacobi_jet_formula (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    nativeJacobiJet p = 2 * actualLegendreJacobi p ^ 2 *
      (evenLogPolynomial p +
        C ((WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) -
          WPActualGaussBottom.fieldHarmonic p (p / 6))) -
      2 * X ^ p * actualLegendreJacobi p * properLegendreJacobi p := by
  rw [actual_native_Jacobi_jet p hp, actual_rankDividedField_eq_hat p hp, rankHatField]
  ring

theorem actual_native_V_conic (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (fieldV p).comp (conic : (ZMod p)[X]) = 1 - Tc ^ 2 := by
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : ZMod p) ≠ 0 := by
    simpa only [show (5 : ZMod p) ^ 3 = 125 by norm_num] using pow_ne_zero 3 h5
  have hu : (125 : (ZMod p)[X]) * C ((1 / 125 : ℚ) : ZMod p) = 1 := by
    change C (125 : ZMod p) * C ((1 / 125 : ℚ) : ZMod p) = 1
    rw [← C_mul]
    norm_num [Rat.cast_def, h125]
  simp only [fieldV, mul_comp, pow_comp, sub_comp, ofNat_comp, one_comp, X_comp, C_comp]
  unfold conic Tc
  linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * hu

/-- The original native V-coordinate retains its proper source and the literal full L_V. -/
theorem actual_native_V_conic_jet (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((nativeJetField p).comp (fieldV p)).comp (conic : (ZMod p)[X]) =
      2 * (actualLegendreJacobi p).comp Tc ^ 2 *
        ((LV p).comp conic - C (WPActualGaussBottom.fieldHarmonic p (p / 6))) -
      2 * Tc ^ p * (actualLegendreJacobi p).comp Tc * (properLegendreJacobi p).comp Tc := by
  have he := congrArg (fun P : (ZMod p)[X] => P.comp Tc)
    (actual_native_Jacobi_jet_formula p hp)
  have hL : (LPsrc p : (ZMod p)[X]) =
      evenLogPolynomial p + C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
    unfold LPsrc evenLogPolynomial EP WPFiniteNC122.q
    ring
  rw [comp_assoc, actual_native_V_conic p hp]
  rw [LV_conic p hp, hL, add_comp, C_comp]
  simp only [nativeJacobiJet, comp_assoc, sub_comp, one_comp, pow_comp, X_comp,
    mul_comp, ofNat_comp, add_comp, C_comp, map_sub] at he
  linear_combination he

end WPActualNativeJacobiJet
