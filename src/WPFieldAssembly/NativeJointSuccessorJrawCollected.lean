import WPFieldAssembly.NativeJointSuccessorEvenResidues
import WPFieldAssembly.NativeJointSuccessorOddOrigin
import WPFieldAssembly.SourceClosureVbalFieldEvaluation

open scoped Polynomial LaurentPolynomial LaurentSeries
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorJrawCollected

open ActualBpairContraction ActualBpairNativeTail ActualCubicNativeSource
open ActualSimplePoleResidue
open ActualKwFiniteHBridge ActualKwOrderedEndpoints ActualRationalSignRows
open NativeClosureMixedSource NativeClosureMixedJ ActualVbalFieldClosure
open NativeJointSuccessorMixedPrimitive NativeJointSuccessorJSeries
open NativeJointSuccessorOddResidues NativeJointSuccessorProductResidues
open NativeJointSuccessorEvenResidues NativeJointSuccessorOddCollection
open NativeJointSuccessorOddOrigin

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The product terms remaining after the actual conic packet and all six ordered H rows. -/
noncomputable def mixedJProduct (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let q := WPFiniteNC122.q (K := K) p
  let h := WPFiniteNC122.h (K := K) p
  let C := WPFifthEntropy.C p u
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  (509 / 25 : K) * q ^ 2 + (316 / 25 : K) * h * q + (197 / 375 : K) * h ^ 2 -
    (62 / 25 : K) * q * C - (149 / 75 : K) * C ^ 2 - (88 / 15 : K) * h * C -
    (44 / 5 : K) * (q - C) * k - (11 / 10 : K) * h * k

private theorem original_even_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (originalEven p : K[X]).eval 0 = WPFifthEntropy.C p u := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  simp only [originalEven, eval_mul, eval_neg, eval_C, ← coeff_zero_eq_eval_zero,
    Dstar_origin_fifth p hp u hu]
  field_simp [h3]

/-- Jraw is collected from its actual odd, even, origin, and full finite-band sources. -/
theorem actual_Jraw_collected_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (11 / 15 : K) * conicPacket p u w -
        (11 / 10 : K) * originalG p (1 / 5) + mixedJHRow p + mixedJProduct p u := by
  rw [actual_Jraw_conic_even_residue p hp u hu, actual_odd_collected_scalar p hp]
  simp only [actual_odd_infinity_origin_harmonic p hp u hu, Tprod_value p hp,
    actual_AK_origin p hp u hu, WPFiniteFifthSourceContraction.actual_a0_fifth p hp u hu,
    actual_even_conic_coordinate p hp w hw, kappa, original_even_origin p hp u hu]
  obtain ⟨ha, hb⟩ := Dstar_endpoints (K := K) p hp
  simp only [originalEven, eval_mul, eval_neg, eval_C, ha, hb]
  dsimp only [mixedJProduct, mixedJHRow, conicPacket, WPFiniteNC122.h, WPFiniteNC122.q,
    WPFiniteJNormalization.r, WPFiniteFifthSourceContraction.k, q2]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by ring]
    exact mul_ne_zero h2 h3
  have h9 : (9 : K) ≠ 0 := by
    rw [show (9 : K) = 3 ^ 2 by ring]
    exact pow_ne_zero 2 h3
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h40 : (40 : K) ≠ 0 := by
    rw [show (40 : K) = 2 ^ 3 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h5
  have h45 : (45 : K) ≠ 0 := by
    rw [show (45 : K) = 3 * 15 by ring]
    exact mul_ne_zero h3 h15
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 25 by ring]
    exact mul_ne_zero h3 h25
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  have h375 : (375 : K) ≠ 0 := by
    rw [show (375 : K) = 3 * 125 by ring]
    exact mul_ne_zero h3 h125
  field_simp [h2, h3, h5, h6, h9, h10, h15, h25, h40, h45, h75, h125, h225, h375]
  ring

/-- The conic packet still contains its genuine Q11 origin term explicitly. -/
theorem actual_Jraw_conic_Q11_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (11 / 15 : K) * originalG p (3 / 11) +
        (44 * WPFiniteNC122.h p / 15) * (WPFiniteField.E p (2 * w) - WPFiniteField.E p w) +
        (22 / 5 : K) * (WPFiniteNC122.q p - WPFifthEntropy.C p u) *
          (WPFiniteInversion.integerFermatQuotient p 11 : K) -
        (11 / 10 : K) * originalG p (1 / 5) + mixedJHRow p + mixedJProduct p u := by
  rw [actual_Jraw_collected_value p hp u w hu hw]
  dsimp only [conicPacket, WPFiniteNC122.h, WPFiniteNC122.q]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  field_simp [h3, h5, h15]
  ring

/-- The explicit collected value retains the ordered H endpoints before their joint contraction. -/
theorem actual_Jraw_six_H_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) =
      (11 / 15 : K) * conicPacket p u w - (11 / 10 : K) * originalG p (1 / 5) -
        (232 / 225 : K) * branchH p (1 / 4) (1 / 4) -
        (76 / 45 : K) * branchH p 4 (1 / 4) +
        (67 / 225 : K) * branchH p (1 / 4) 4 +
        (2 / 9 : K) * branchH p 4 4 +
        (176 / 75 : K) * branchH p 0 (1 / 4) -
        (11 / 75 : K) * branchH p 0 4 +
        (509 / 25 : K) * WPFiniteNC122.q p ^ 2 +
        (316 / 25 : K) * WPFiniteNC122.h p * WPFiniteNC122.q p +
        (197 / 375 : K) * WPFiniteNC122.h p ^ 2 -
        (62 / 25 : K) * WPFiniteNC122.q p * WPFifthEntropy.C p u -
        (149 / 75 : K) * WPFifthEntropy.C p u ^ 2 -
        (88 / 15 : K) * WPFiniteNC122.h p * WPFifthEntropy.C p u -
        (44 / 5 : K) * (WPFiniteNC122.q p - WPFifthEntropy.C p u) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) -
        (11 / 10 : K) * WPFiniteNC122.h p *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) := by
  rw [actual_Jraw_collected_value p hp u w hu hw]
  dsimp only [mixedJHRow, mixedJProduct]
  ring

end WPFieldAssembly.NativeJointSuccessorJrawCollected
