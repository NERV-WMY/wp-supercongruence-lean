import WPFieldAssembly.NativeClosureMetricCarrier
import WPFieldAssembly.NativeClosureMetricEnds
import WPFieldAssembly.NativeClosureMetricKernel
import WPFieldAssembly.NativeClosureMetricEulerShift
import WPFieldAssembly.NativeClosureGaussM

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2200000

/-- The whole cleared metric expression retains the kernel, both Euler bands and origin logarithm. -/
noncomputable def metricClearedOrigin (p : ℕ) [Fact p.Prime]
    (m g : (ZMod p)[X]) : ZMod p :=
  (-m.toLaurent * (1 - LaurentPolynomial.C (2 / 3 : ZMod p) * T (-(p : ℤ))) *
      D (literalKB (K := ZMod p) p)).coeff (-1) -
    originPole ((LaurentPolynomial.C (5 / 24 : ZMod p) * T (p : ℤ) *
      (4 * T (p : ℤ) - 11) + LaurentPolynomial.C (1 / 9 : ZMod p) *
        (4 * T (-(p : ℤ)) - 11)) * metricDuCleared p m g) -
    (25 / 18 : ZMod p) * originPole (metricDvCleared p m g) +
    (55 / 24 : ZMod p) * originPole (T (p : ℤ) * metricDvCleared p m g) +
    (-LaurentPolynomial.C (1 / 6 : ZMod p) * (4 * T (-(p : ℤ)) - 11) *
      T (-1) * m.toLaurent).coeff (-1)

/-- Cancellation of m(0) occurs after the full metric source has been collected. -/
theorem metricClearedOrigin_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (m g : (ZMod p)[X]) (hm : m.natDegree ≤ p - 2)
    (hg : g.natDegree ≤ (p - 1) / 2 - 2)
    (ha : g.eval (1 / 4) = 4 * m.eval (1 / 4)) (hb : g.eval 4 = m.eval 4) :
    metricClearedOrigin p m g =
      (1199 / 450 : ZMod p) * m.eval (1 / 4) - (583 / 225 : ZMod p) * m.eval 4 := by
  have hk := metric_original_KB_pair p hp m hm
  have he := metric_complete_euler_origin_collector p hp m g hm hg ha hb
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1; norm_num
  have h18 : (18 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 (pow_ne_zero 2 h3) using 1; norm_num
  have h36 : (36 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h4 (pow_ne_zero 2 h3) using 1; norm_num
  have h75 : (75 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h3 (pow_ne_zero 2 h5) using 1; norm_num
  have h100 : (100 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h4 (pow_ne_zero 2 h5) using 1; norm_num
  have h225 : (225 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h3) (pow_ne_zero 2 h5) using 1; norm_num
  have h450 : (450 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h225 using 1; norm_num
  dsimp only [metricClearedOrigin]
  linear_combination (norm := (field_simp [h4, h18, h36, h75, h100, h225, h450]; ring)) hk + he

/-- The proper metric endpoints are evaluations of the same actual M primitive. -/
theorem actual_hand_metric_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualHandMetric p).eval (1 / 4) = -(ActualFirstGreen.M p).eval 1 / 10 ∧
      (actualHandMetric p).eval 4 = (ActualFirstGreen.M p).eval 1 / 5 := by
  obtain ⟨ha, hb⟩ := actual_CM_endpoints_from_M p hp
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1; norm_num
  have h20 : (20 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h10 using 1; norm_num
  constructor
  · simp only [actualHandMetric, eval_mul, eval_C, ha]
    field_simp [h10, h20]
    ring
  · simp only [actualHandMetric, eval_mul, eval_C, hb]
    field_simp [h5, h10]
    ring

/-- The actual metric contraction, before the independently required Gauss value M(1). -/
theorem actual_metric_cleared_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    metricClearedOrigin p (actualHandMetric p) (actualMetricCore p) =
      -(1177 / 1500 : ZMod p) * (ActualFirstGreen.M p).eval 1 := by
  obtain ⟨hga, hgb⟩ := actual_metric_core_end_relations p hp
  rw [metricClearedOrigin_endpoints p hp _ _ (actual_hand_metric_degree p hp)
    (actual_metric_core_degree p hp) hga hgb]
  obtain ⟨ha, hb⟩ := actual_hand_metric_endpoints p hp
  rw [ha, hb]
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1; norm_num
  have h225 : (225 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h3) (pow_ne_zero 2 h5) using 1; norm_num
  have h450 : (450 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h225 using 1; norm_num
  have h1500 : (1500 : ZMod p) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 2 h2)
      (mul_ne_zero h3 (pow_ne_zero 3 h5)) using 1; norm_num
  field_simp [h5, h10, h225, h450, h1500]
  ring

/-- The whole cleared actual metric now uses the proved endpoint of the same M. -/
theorem actual_metric_cleared_gauss_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    metricClearedOrigin p (actualHandMetric p) (actualMetricCore p) =
      -(1177 / 750 : ZMod p) * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 := by
  rw [actual_metric_cleared_value p hp, NativeClosureGaussM.actual_M_endpoint p hp]
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h750 : (750 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 (mul_ne_zero h3 (pow_ne_zero 3 h5)) using 1; norm_num
  have h1500 : (1500 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h750 using 1; norm_num
  field_simp [h750, h1500]
  ring

end WPFieldAssembly.ActualBpairContraction
