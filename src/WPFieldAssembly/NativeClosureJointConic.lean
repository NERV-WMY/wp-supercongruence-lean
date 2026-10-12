import WPFieldAssembly.NativeClosureMetricCarrier
import WPFieldAssembly.ActualEtaTransport
import WPFieldAssembly.NativeClosureThreePhaseConic
import WPFieldAssembly.ActualBpairBranchSquare
import WPFieldAssembly.NativeClosureGaussM

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPPIntegralReduction WPFiniteWSource
open WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.NativeEulerPrimitive WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2400000

/- The direct support estimate yields the sufficient p-4-delta bound below.
   It does not establish the printed stronger p-5-delta cancellation.
   Preserve the rejected, formerly unchecked p=19 illustration (d=3,n=9):
   native b_3=8, cubic top=2, H(V) top=15, PM(V) top=4,
   branchPolynomial top=2. The two degree-15 contributions would be
   18*4*4=3 and 8*15*2=12 in ZMod 19, hence 15 rather than zero.
   The exact native_mixed_j_lowest_certificate.py replay corrects branch top
   to 9: the two degree-15 terms are 3 and 16, and cancel in ZMod 19;
   the actual PC has degree 7. The old illustration refutes no stronger bound.
   This finite [ONE] calculation is not used by the Lean theorem. -/

/-- The joint CM/H coefficient is a polynomial from the actual sources, before any residue. -/
noncomputable def actualGreenPC (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  Polynomial.C (1 / 75 : ZMod p) * X ^ ((p - 1) / 2 - 1) * (4 * X - 11) *
      (quadraticInverse (ActualFirstGreen.M p).divX).comp
        (WPHasseIntegralTransport.fieldV p) +
    Polynomial.C (2 / 5 : ZMod p) * ActualGreenResidue.Hpull p * branchPolynomial p

/-- Lean CM is half the hand CM; the whole joint branch factor is exact. -/
theorem actualGreenPC_factor (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    T (((p - 1) / 2 - 1 : ℕ) : ℤ) *
        (LaurentPolynomial.C (2 / 3 : ZMod p) * (ActualFirstGreen.CM p).toLaurent +
          LaurentPolynomial.C (2 / 5 : ZMod p) *
            (ActualGreenResidue.Hpull p).toLaurent * Dsym p) =
      (squaredCoordinate : (ZMod p)[X]).toLaurent ^ (((p - 1) / 2) + 1) *
        (actualGreenPC p).toLaurent := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h50 : (50 : ZMod p) ≠ 0 := by
    rw [show (50 : ZMod p) = 2 * 5 ^ 2 by norm_num]
    exact mul_ne_zero h2 (pow_ne_zero 2 h5)
  have h75 : (75 : ZMod p) ≠ 0 := by
    rw [show (75 : ZMod p) = 3 * 5 ^ 2 by norm_num]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have hc : (2 / 3 : ZMod p) * (1 / 50) = 1 / 75 := by
    field_simp [h3, h50, h75]
    ring
  have hC := congrArg (LaurentPolynomial.C : ZMod p → (ZMod p)[T;T⁻¹]) hc
  rw [map_mul] at hC
  have hb := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (branchPolynomial_factor (K := ZMod p) p hp)
  rw [branchNumerator_toLaurent p hp] at hb
  simp only [map_mul, map_pow] at hb
  have hm := congrArg (fun P : (ZMod p)[X] => P.toLaurent) (actual_CM_PM_source p hp)
  simp only [map_mul, map_pow, Polynomial.toLaurent_C] at hm
  rw [hm]
  simp only [actualGreenPC, map_add, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X_pow]
  linear_combination
    (LaurentPolynomial.C (2 / 5 : ZMod p) * (ActualGreenResidue.Hpull p).toLaurent) * hb +
      (T (((p - 1) / 2 - 1 : ℕ) : ℤ) *
        squaredCoordinate.toLaurent ^ (((p - 1) / 2) + 1) *
        (4 * X - 11 : (ZMod p)[X]).toLaurent *
        ((quadraticInverse (ActualFirstGreen.M p).divX).comp
          (WPHasseIntegralTransport.fieldV p)).toLaurent) * hC

/-- The actual source gives the sufficient p-4 bound; no stronger unproved cancellation is used. -/
theorem actualGreenPC_degree (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualGreenPC p).natDegree ≤ p - 4 := by
  let n := (p - 1) / 2
  let d := p / 6
  have hV : (WPHasseIntegralTransport.fieldV p).natDegree ≤ 3 := by
    unfold WPHasseIntegralTransport.fieldV
    compute_degree
  have hPM : (quadraticInverse (ActualFirstGreen.M p).divX).natDegree ≤ d - 1 := by
    exact actual_PM_degree p hp
  have hPMV : ((quadraticInverse (ActualFirstGreen.M p).divX).comp
      (WPHasseIntegralTransport.fieldV p)).natDegree ≤ 3 * (d - 1) :=
    natDegree_comp_le.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hPM hV)
  have hH : (ActualGreenResidue.Hpull p).natDegree ≤ 3 * d := by
    unfold ActualGreenResidue.Hpull
    exact natDegree_comp_le.trans
      (by simpa only [Nat.mul_comm] using Nat.mul_le_mul (nativeHField_degree p) hV)
  have hb := branchPolynomial_degree (K := ZMod p) p hp
  have hlin : (4 * X - 11 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
  have hfirst : (Polynomial.C (1 / 75 : ZMod p) * X ^ (n - 1) * (4 * X - 11) *
      (quadraticInverse (ActualFirstGreen.M p).divX).comp
        (WPHasseIntegralTransport.fieldV p)).natDegree ≤ (n - 1) + 1 + 3 * (d - 1) := by
    apply natDegree_mul_le_of_le _ hPMV
    apply natDegree_mul_le_of_le _ hlin
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hsecond : (Polynomial.C (2 / 5 : ZMod p) * ActualGreenResidue.Hpull p *
      branchPolynomial p).natDegree ≤ 3 * d + (n - 3) :=
    natDegree_mul_le_of_le ((natDegree_C_mul_le _ _).trans hH) hb
  have hs := (natDegree_add_le _ _).trans (max_le_max hfirst hsecond)
  change (actualGreenPC p).natDegree ≤ _ at hs
  exact hs.trans (max_le (by dsimp [n, d]; omega) (by dsimp [n, d]; omega))

/-- The quotient keeps the actual odd metric normalization at its zero argument. -/
theorem actual_PM_origin_metric_end (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (quadraticInverse (ActualFirstGreen.M p).divX).eval 0 =
      (ActualFirstGreen.M p).eval 1 := by
  have h := congrArg (fun P : (ZMod p)[X] => P.eval 1) (actual_PM_M_source p hp)
  simpa only [eval_mul, eval_X, eval_comp, eval_sub, eval_one, eval_pow,
    one_pow, sub_self, one_mul] using h.symm

/-- Both original endpoint values belong to the whole joint coefficient. -/
theorem actualGreenPC_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (actualGreenPC p).eval (1 / 4) = -8 * (ActualFirstGreen.M p).eval 1 / 15 ∧
      (actualGreenPC p).eval 4 = (ActualFirstGreen.M p).eval 1 / 60 := by
  let n := (p - 1) / 2
  have h4 : (4 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have hn : 1 ≤ n := by dsimp [n]; omega
  have h4n : (4 : ZMod p) ^ n = 1 := four_half_power p hp
  have han : (1 / 4 : ZMod p) ^ n = 1 := by rw [div_pow, one_pow, h4n, div_one]
  have hbm : (4 : ZMod p) ^ (n - 1) = 1 / 4 := by
    apply (eq_div_iff h4).2
    rw [← pow_succ, Nat.sub_add_cancel hn, h4n]
  have ham : (1 / 4 : ZMod p) ^ (n - 1) = 4 := by
    apply mul_right_cancel₀ (one_div_ne_zero h4)
    rw [← pow_succ, Nat.sub_add_cancel hn, han, mul_one_div_cancel h4]
  have hφ : ActualThreePhase.φ (K := ZMod p) p = RingHom.id (ZMod p) :=
    Subsingleton.elim _ _
  have hH := (ActualGreenResidue.actual_native_pullback_facts (K := ZMod p) p hp).2.2.2
  simp only [ActualGreenResidue.HpullK, hφ, Polynomial.map_id] at hH
  have hVa : (WPHasseIntegralTransport.fieldV p).eval (1 / 4) = 0 := by
    simp [WPHasseIntegralTransport.fieldV, mul_inv_cancel₀ h4]
  have hVb : (WPHasseIntegralTransport.fieldV p).eval 4 = 0 := by
    simp [WPHasseIntegralTransport.fieldV]
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : ZMod p) ≠ 0 := by
    rw [show (15 : ZMod p) = 3 * 5 by norm_num]
    exact mul_ne_zero h3 h5
  have h60 : (60 : ZMod p) ≠ 0 := by
    rw [show (60 : ZMod p) = 4 * 15 by norm_num]
    exact mul_ne_zero h4 h15
  have h75 : (75 : ZMod p) ≠ 0 := by
    rw [show (75 : ZMod p) = 3 * 5 ^ 2 by norm_num]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  constructor
  · simp only [actualGreenPC, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      eval_sub, eval_ofNat, eval_comp, hVa, hH.1, zero_mul, mul_zero, add_zero,
      actual_PM_origin_metric_end p hp, show (p - 1) / 2 - 1 = n - 1 from rfl, ham]
    field_simp [h4, h15, h75]
    ring
  · simp only [actualGreenPC, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      eval_sub, eval_ofNat, eval_comp, hVb, hH.2, zero_mul, mul_zero, add_zero,
      actual_PM_origin_metric_end p hp, show (p - 1) / 2 - 1 = n - 1 from rfl, hbm]
    field_simp [h4, h60, h75]
    ring

/-- The whole actual joint conic source reaches the same proper metric endpoint. -/
theorem actual_joint_conic_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originPole (threePhaseConicDensity p (actualGreenPC p)) =
      -3 * (ActualFirstGreen.M p).eval 1 / 125 := by
  obtain ⟨ha, hb⟩ := actualGreenPC_endpoints p hp
  exact threePhaseConic_metric_ends p hp _
    ((actualGreenPC_degree p hp).trans (by omega)) _ ha hb

/-- The original joint conic source uses the actual, independently identified M endpoint. -/
theorem actual_joint_conic_gauss_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    originPole (threePhaseConicDensity p (actualGreenPC p)) =
      -6 * WPActualGaussBottom.fieldHarmonic p (p / 6) ^ 2 / 125 := by
  rw [actual_joint_conic_origin p hp, NativeClosureGaussM.actual_M_endpoint p hp]
  ring

end WPFieldAssembly.ActualBpairContraction
