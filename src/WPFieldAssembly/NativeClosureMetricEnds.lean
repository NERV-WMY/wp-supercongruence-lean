import WPFieldAssembly.ActualFirstGreen

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteJHighCoefficient WPFiniteCubicLog

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

/-- Both metric endpoints come from the same odd M carrier, before its Gauss value is used. -/
theorem actual_CM_endpoints_from_M (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ActualFirstGreen.CM p).eval (1 / 4) = -(ActualFirstGreen.M p).eval 1 / 20 ∧
      (ActualFirstGreen.CM p).eval 4 = (ActualFirstGreen.M p).eval 1 / 10 := by
  obtain ⟨_, _, _, _, _, _, hMreflect, _⟩ := ActualFirstGreen.actual_low_primitive p hp
  have hMneg : (ActualFirstGreen.M p).eval (-1) = -(ActualFirstGreen.M p).eval 1 := by
    simpa only [eval_comp, eval_neg, eval_X] using
      congrArg (fun P : (ZMod p)[X] => P.eval 1) hMreflect
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h20 : (20 : ZMod p) ≠ 0 := by
    rw [show (20 : ZMod p) = 2 * 10 by norm_num]
    exact mul_ne_zero h2 h10
  have hca : (conic : (ZMod p)[X]).eval (1 / 2) = 1 / 4 := by
    simp only [conic, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X, eval_one]
    field_simp [h2, h4]
    ring
  have hta : (Tc : (ZMod p)[X]).eval (1 / 2) = -1 := by
    simp only [Tc, eval_sub, eval_mul, eval_ofNat, eval_pow, eval_X]
    field_simp [h2]
    ring
  have hpa : (1 / 2 : ZMod p) ^ p = 1 / 2 := ZMod.pow_card _
  have ha := congrArg (fun P : (ZMod p)[X] => P.eval (1 / 2))
    (ActualFirstGreen.actual_carrier_pullbacks p hp).2
  simp only [eval_comp, ActualFirstGreen.CMt, eval_mul, eval_C, eval_pow, eval_X] at ha
  rw [hca, hta, hpa, hMneg] at ha
  have hb := congrArg (fun P : (ZMod p)[X] => P.eval 1)
    (ActualFirstGreen.actual_carrier_pullbacks p hp).2
  simp only [eval_comp, ActualFirstGreen.CMt, eval_mul, eval_C, eval_pow, eval_X] at hb
  norm_num [conic, Tc] at hb
  constructor
  · rw [ha]
    field_simp [h2, h10, h20]
    ring
  · rw [hb]
    ring

end WPFieldAssembly.ActualBpairContraction
