import WPFieldAssembly.ActualFirstGreen
import WPFieldAssembly.NativeOriginalResidues

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteWSource WPFiniteJHighCoefficient WPFiniteCubicLog
open WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2200000

/-- The actual odd primitive gives an even quotient without assigning a source. -/
theorem actual_M_divX_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ActualFirstGreen.M p).divX.comp (-X) = (ActualFirstGreen.M p).divX := by
  rcases ActualFirstGreen.actual_low_primitive p hp with ⟨_, _, _, _, _, h0, he, _⟩
  have hd : X * (ActualFirstGreen.M p).divX = ActualFirstGreen.M p := by
    simpa only [h0, map_zero, add_zero] using X_mul_divX_add (ActualFirstGreen.M p)
  have hr := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hd
  simp only [mul_comp, X_comp, he] at hr
  apply mul_left_cancel₀ (neg_ne_zero.mpr (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
  linear_combination hr + hd

/-- The quadratic inverse recovers the same M with its true zero origin. -/
theorem actual_PM_M_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualFirstGreen.M p = X *
      (quadraticInverse (ActualFirstGreen.M p).divX).comp (1 - X ^ 2) := by
  let Q := (ActualFirstGreen.M p).divX
  have hQ : Q.comp (-X) = Q := actual_M_divX_even p hp
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hcontract : (contract 2 Q).comp (X ^ 2) = Q := by
    rw [← expand_eq_comp_X_pow]
    ext n
    rw [coeff_expand (by norm_num : 0 < 2)]
    by_cases hn : 2 ∣ n
    · rw [if_pos hn, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hn]
    · rw [if_neg hn]
      have ho : Odd n := (Nat.even_or_odd n).resolve_left
        (by rintro ⟨a, ha⟩; exact hn ⟨a, by omega⟩)
      have he := congrArg (fun P : (ZMod p)[X] => P.coeff n) hQ
      rw [WPFieldAssembly.ConicKernel.coeff_comp_neg, ho.neg_pow, one_pow] at he
      have hz : (2 : ZMod p) * Q.coeff n = 0 := by linear_combination -he
      exact ((mul_eq_zero.mp hz).resolve_left h2).symm
  have hi : (quadraticInverse Q).comp (1 - X ^ 2) = Q := by
    rw [quadraticInverse, comp_assoc]
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel]
    exact hcontract
  rcases ActualFirstGreen.actual_low_primitive p hp with ⟨_, _, _, _, _, h0, _, _⟩
  rw [hi]
  symm
  simpa only [h0, map_zero, add_zero] using X_mul_divX_add (ActualFirstGreen.M p)

/-- The degree of the actual quadratic quotient is determined before taking residues. -/
theorem actual_PM_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (quadraticInverse (ActualFirstGreen.M p).divX).natDegree ≤ p / 6 - 1 := by
  apply WPFieldAssembly.NativeOriginalResidues.quadraticInverse_degree_of_le
  rw [natDegree_divX_eq_natDegree_tsub_one]
  have hm := (ActualFirstGreen.actual_low_primitive p hp).2.2.2.2.2.2.2
  omega

/-- Lean's CM is half the hand C_M; this is its actual complete polynomial source. -/
theorem actual_CM_PM_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualFirstGreen.CM p = C (1 / 50 : ZMod p) *
      (squaredCoordinate : (ZMod p)[X]) ^ (((p - 1) / 2) + 1) *
      (4 * X - 11) * (quadraticInverse (ActualFirstGreen.M p).divX).comp
        (WPHasseIntegralTransport.fieldV p) := by
  have h5 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h2 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h10 : (10 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1
    norm_num
  have h50 : (50 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h10 h5 using 1
    norm_num
  have hc : (C (1 / 50 : ZMod p) : (ZMod p)[X]) * 5 = C (1 / 10 : ZMod p) := by
    change C (1 / 50 : ZMod p) * C 5 = C (1 / 10 : ZMod p)
    rw [← C_mul]
    congr 1
    field_simp [h10, h50]
    norm_num
  have hcd : (conic : (ZMod p)[X]).natDegree = 2 := by
    unfold conic
    compute_degree
    exact h5
  apply comp_injective_nonconstant
    (conic : (ZMod p)[X]) (by rw [hcd]; norm_num)
  dsimp only
  have hV : (WPHasseIntegralTransport.fieldV p).comp conic =
      1 - (Tc : (ZMod p)[X]) ^ 2 := WPActualNativeJacobiJet.actual_native_V_conic p hp
  have hl : (4 * X - 11 : (ZMod p)[X]).comp conic = 5 * (4 * X ^ 2 - 3) := by
    simp only [conic, sub_comp, mul_comp, ofNat_comp, X_comp]
    ring
  have hn : 2 * (((p - 1) / 2) + 1) = p + 1 := by
    have := half_exponent p hp
    omega
  have hs : ((squaredCoordinate : (ZMod p)[X]) ^ (((p - 1) / 2) + 1)).comp conic =
      X ^ (p + 1) := by
    rw [pow_comp, squaredCoordinate_conic p hp, ← pow_mul, hn]
  have hm := congrArg (fun P : (ZMod p)[X] => P.comp Tc)
    (actual_PM_M_source p hp)
  simp only [mul_comp, X_comp, comp_assoc, sub_comp, one_comp, pow_comp] at hm
  rw [(ActualFirstGreen.actual_carrier_pullbacks p hp).2, ActualFirstGreen.CMt, hm]
  rw [mul_comp, mul_comp, mul_comp, C_comp, hs, hl, comp_assoc, hV]
  rw [pow_succ (X : (ZMod p)[X]) p]
  have ht : (Tc : (ZMod p)[X]) = X * (4 * X ^ 2 - 3) := by
    unfold Tc
    ring
  linear_combination
    (C (1 / 10 : ZMod p) * X ^ p *
      (quadraticInverse (ActualFirstGreen.M p).divX).comp (1 - Tc ^ 2)) * ht -
    (X ^ p * X * (4 * X ^ 2 - 3)) *
      (quadraticInverse (ActualFirstGreen.M p).divX).comp (1 - Tc ^ 2) * hc

/-- The original hand metric, rather than a freely chosen polynomial. -/
noncomputable def actualHandMetric (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C (2 : ZMod p) * ActualFirstGreen.CM p

/-- The full quotient left after the same squared-coordinate factor. -/
noncomputable def actualMetricCore (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C (1 / 25 : ZMod p) * (4 * X - 11) *
    (quadraticInverse (ActualFirstGreen.M p).divX).comp (WPHasseIntegralTransport.fieldV p)

theorem actual_hand_metric_factor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualHandMetric p = squaredCoordinate ^ (((p - 1) / 2) + 1) * actualMetricCore p := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : ZMod p) ≠ 0 := by
    rw [show (25 : ZMod p) = 5 ^ 2 by norm_num]; exact pow_ne_zero 2 h5
  have h50 : (50 : ZMod p) ≠ 0 := by
    rw [show (50 : ZMod p) = 2 * 5 ^ 2 by norm_num]; exact mul_ne_zero h2 (pow_ne_zero 2 h5)
  have hc : (2 : ZMod p) * (1 / 50) = 1 / 25 := by
    field_simp [h25, h50]; ring
  have hC := congrArg (Polynomial.C : ZMod p → (ZMod p)[X]) hc
  rw [map_mul] at hC
  rw [actualHandMetric, actual_CM_PM_source p hp]
  unfold actualMetricCore
  linear_combination squaredCoordinate ^ (((p - 1) / 2) + 1) * (4 * X - 11) *
    (quadraticInverse (ActualFirstGreen.M p).divX).comp (WPHasseIntegralTransport.fieldV p) * hC

theorem actual_metric_core_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualMetricCore p).natDegree ≤ (p - 1) / 2 - 2 := by
  have hV : (WPHasseIntegralTransport.fieldV p).natDegree ≤ 3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  have hc := natDegree_comp_le.trans (Nat.mul_le_mul (actual_PM_degree p hp) hV)
  have hl : (4 * X - 11 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have hg : (actualMetricCore p).natDegree ≤ 1 + (p / 6 - 1) * 3 :=
    natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hl) hc
  have hh := half_exponent p hp
  exact hg.trans (by omega)

theorem actual_hand_metric_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHandMetric p).natDegree ≤ p - 2 := by
  have hs : (squaredCoordinate : (ZMod p)[X]).natDegree ≤ 1 := by
    unfold squaredCoordinate
    compute_degree
  rw [actual_hand_metric_factor p hp]
  have hpow := natDegree_pow_le_of_le (((p - 1) / 2) + 1) hs
  have hprod := natDegree_mul_le_of_le hpow (actual_metric_core_degree p hp)
  exact hprod.trans (by omega)

/-- The two quotient evaluations come from the same carrier factor at the actual ends. -/
theorem actual_metric_core_end_relations (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualMetricCore p).eval (1 / 4) = 4 * (actualHandMetric p).eval (1 / 4) ∧
      (actualMetricCore p).eval 4 = (actualHandMetric p).eval 4 := by
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hsa : (squaredCoordinate : (ZMod p)[X]).eval (1 / 4) = 1 / 4 := by
    simp only [squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [h4, h5]; ring
  have hsb : (squaredCoordinate : (ZMod p)[X]).eval 4 = 1 := by
    simp only [squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
    field_simp [h5]; ring
  have haN : (1 / 4 : ZMod p) ^ ((p - 1) / 2) = 1 := by
    rw [div_pow, one_pow, four_half_power p hp, div_one]
  have ha := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 4))
    (actual_hand_metric_factor p hp)
  have hb := congrArg (fun P : (ZMod p)[X] => P.eval 4)
    (actual_hand_metric_factor p hp)
  rw [eval_mul, eval_pow, hsa, pow_succ, haN, one_mul] at ha
  rw [eval_mul, eval_pow, hsb, one_pow, one_mul] at hb
  constructor
  · linear_combination (norm := (field_simp [h4]; ring)) -4 * ha
  · exact hb.symm

/-- The actual cleared source keeps the full p-th power before residue extraction. -/
theorem actual_metric_frobenius_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    actualHandMetric p * squaredCoordinate ^ ((p - 1) / 2) =
      C (1 / 5 : ZMod p) * (X ^ p + 1) * actualMetricCore p := by
  have hh : (((p - 1) / 2) + 1) + ((p - 1) / 2) = p := by
    have := half_exponent p hp
    omega
  have hs : (squaredCoordinate : (ZMod p)[X]) ^ p =
      C (1 / 5 : ZMod p) * (X ^ p + 1) := by
    simp only [squaredCoordinate, mul_pow, add_pow_char, one_pow, ← map_pow,
      ZMod.pow_card, one_div]
  rw [actual_hand_metric_factor p hp]
  calc
    _ = (squaredCoordinate : (ZMod p)[X]) ^ p * actualMetricCore p := by
      calc
        _ = (squaredCoordinate : (ZMod p)[X]) ^
            ((((p - 1) / 2) + 1) + ((p - 1) / 2)) * actualMetricCore p := by
          rw [pow_add]
          ring
        _ = _ := by rw [hh]
    _ = _ := by rw [hs]

end WPFieldAssembly.ActualBpairContraction
