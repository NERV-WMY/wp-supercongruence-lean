import WPFieldAssembly.NativeJointSuccessorC3
import WPFieldAssembly.NativeJointSuccessorFiniteAlphabet
import WPFieldAssembly.SourceClosureNormalizedZFinite
import WPFieldAssembly.ScalarFinalSuccessorWholeTraceAlphabet
import WPFieldAssembly.SourceClosureUVOrderedH
import WPFieldAssembly.SourceClosureUVFiniteEnds
import WPFieldAssembly.NativeScalarRows

open scoped Polynomial LaurentPolynomial
open Polynomial

namespace WPFieldAssembly.NativeJointSuccessorB2Finite

open ActualBpairContraction ActualKwOrderedEndpoints ActualVbalFieldClosure
open ActualSimplePoleResidue ActualUVSourceIdentification ActualKwWeightedTrace
open SourceClosureUVOrderedH SourceClosureUVFiniteEnds SourceClosureUVDescent
open SourceClosurePSquareTail SourceClosureNormalizedZFinite SourceClosureWholeTraceCollection
open NativeClosureMixedSource NativeClosureMixedJ NativeJointSuccessorC3
open WPFiniteProductTail WPFiniteABSourceTail WPFiniteWSource
open WPFiniteJNormalization WPFiniteJHighCoefficient

variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000

/-- The three original normalized-Z primitive terms, with their original epsilon. -/
noncomputable def normalizedZPrimitiveRow (p : ℕ) : K :=
  -22 * originalPSquareHRow p / (15 * epsilon p) +
    8 * (2 * (JdifferenceP p (W p)).eval (1 / 4) +
      (JdifferenceP p (W p)).eval 4) / (15 * epsilon p) -
    69 * (originPrimitive p (W p) (1 / 4) - originPrimitive p (W p) 4) /
      (5 * epsilon p)

/-- The remaining actual normalized-Z scalar, before any J-origin cancellation. -/
noncomputable def normalizedZWithoutH (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K :=
  -WPFiniteField.R p (16 : K) / 30 - 159 * WPFiniteNC122.q p ^ 2 / 25 +
    129 * WPFiniteNC122.q p * WPFiniteJNormalization.r p / 25 -
    9 * WPFiniteJNormalization.r p ^ 2 / 10 -
    2 * WPFiniteNC122.q p * WPFiniteField.ell p (16 : K) / 25 -
    11 * WPFiniteJNormalization.r p * WPFiniteField.ell p (16 : K) / 100 +
    119 * WPFifthEntropy.C p u ^ 2 / 25 + 92 * WPFiniteNC122.q p * WPFifthEntropy.C p u / 25 +
    11 * U_J p u / 15 - 22 * V_J p u / 15

/-- Every actual W-unit primitive is attached to the same ordered branch primitive. -/
theorem actual_W_unit_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c y : K) :
    (unitPrimitiveP p (W p) c).eval y =
      (2 * epsilon p / 15 : K) * branchH p c y := by
  rw [original_unitPrimitive_movingH p hp, ← branchH_movingH p hp]

/-- The zero-pole primitive keeps its full original finite origin source. -/
theorem actual_W_origin_branch (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (y : K) :
    originPrimitive p (W p) y = (2 * epsilon p / 15 : K) * branchH p 0 y := by
  rw [← unitPrimitive_origin, ← unitPrimitiveP_eval, actual_W_unit_branch p hp]

/-- The actual three primitive terms collect to the original six ordered HPJ coefficients. -/
theorem actual_normalized_Z_HPJ_row (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    normalizedZPrimitiveRow (K := K) p = HPJRow p := by
  dsimp only [normalizedZPrimitiveRow, originalPSquareHRow, originalHa, originalHb, originalHx]
  rw [JdifferenceP_eval, JdifferenceP_eval]
  simp only [← unitPrimitiveP_eval, actual_W_unit_branch p hp, actual_W_origin_branch p hp]
  rw [HPJRow]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero 2 h2
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h225 : (225 : K) ≠ 0 := by
    rw [show (225 : K) = 15 ^ 2 by ring]
    exact pow_ne_zero 2 h15
  have heps : (epsilon p : K) ≠ 0 := pow_ne_zero _ h5
  field_simp [h2, h3, h4, h5, h15, h225, heps]
  ring

/-- The actual normalized Z uses its original primitive row and the genuine descended C. -/
theorem actual_normalized_Z_HPJ (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    normalizedZFiniteValue p u = HPJRow p + normalizedZWithoutH p u := by
  rw [← actual_normalized_Z_HPJ_row p hp]
  dsimp only [normalizedZFiniteValue, normalizedZPrimitiveRow, normalizedZWithoutH]
  simp only [← originalC_descended p hp u hu]
  ring

/-- The two literal J-origin identities identify h0J, without assigning any HJP coefficient. -/
theorem actual_h0J_UV_split (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteNC122.h0J p u = U_J p u / 5 + V_J p u := by
  rw [← WPFiniteJSource.HJP_origin p hp u hu]
  exact WPFiniteJHighCoefficient.actual_J_origin_split p hp u hu

/-- The same GKQ source cancels the original V_J term at its actual weight. -/
theorem actual_GKQ_J_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    NativeScalarRows.actualGKQ p + 11 * U_J p u / 15 - 22 * V_J p u / 15 =
      2 * WPFiniteNC122.Aeven p (WPFiniteNC122.T0 u) -
        4 * WPFiniteNC122.a0 p u ^ 2 / 3 +
        2 * (WPFiniteNC122.q p - WPFiniteNC122.h p) * WPFiniteNC122.a0 p u -
        2 * WPFiniteNC122.h p ^ 2 / 3 + 2 * WPFiniteNC122.q p * WPFiniteNC122.h p -
        WPFiniteNC122.q p ^ 2 + 77 * U_J p u / 75 := by
  rw [NativeScalarRows.actual_GKQ_corrected_value p hp u hu, actual_h0J_UV_split p hp u hu]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  field_simp [h3, h5, h15, h75]
  ring

/-- The complete two D_N zero-pole terms become Ke minus Aeven, including their diagonals. -/
theorem actual_UV_D_difference (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteLoop.D ((p - 1) / 2) (4 / 5 : K) 0 -
        WPFiniteLoop.D ((p - 1) / 2) (1 / 5 : K) 0 =
      4 * (WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u -
        (WPFiniteNC122.Aeven p (2 * u) - WPFiniteNC122.Aeven p u)) := by
  have hu2 : (2 * u) ^ 2 = (4 / 5 : K) := by rw [mul_pow, hu]; ring
  have hd2 := D_half_square_zero_right p hp (2 * u)
  have hd1 := D_half_square_zero_right p hp u
  rw [hu2] at hd2
  rw [hu] at hd1
  rw [hd2, hd1, WPFiniteField.Ke, WPFiniteField.Ke, WPFiniteNC122.Aeven,
    WPFiniteNC122.Aeven]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2]
  ring

/-- The original evenSquared endpoint is evaluated through its whole square substitution. -/
theorem actual_UV_even_endpoint (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    (WPFiniteLVSource.evenSquared p : K[X]).eval (4 / 5) =
      6 * WPFifthEntropy.C p u / 5 - 6 * WPFiniteNC122.q p / 5 +
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 := by
  have hu2 : (2 * u) ^ 2 = (4 / 5 : K) := by rw [mul_pow, hu]; ring
  have hs := congrArg (fun P : K[X] => P.eval (2 * u))
    (WPFiniteLVSource.evenSquared_square (K := K) p hp)
  simp only [eval_comp, eval_pow, eval_X, hu2] at hs
  have he : (WPFiniteKSource.EP p : K[X]).eval (2 * u) = WPFiniteField.E p (2 * u) := by
    simp only [WPFiniteKSource.EP, eval_mul, eval_C, eval_add, eval_comp, eval_neg,
      eval_X, WPFiniteAffineLog.LP_eval_eq, WPFiniteField.E, div_eq_mul_inv]
    ring
  rw [hs, he, WPFifthEntropy.E_at_double_fifth, WPFifthEntropy.E_at_fifth p hp u hu]
  dsimp only [WPFiniteNC122.q]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2, h5]
  ring

private theorem actual_R_four (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.R p (4 : K) = -6 * WPFiniteNC122.q p ^ 2 - 2 * WPFiniteField.R p (-2 : K) := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K)
    (WPFiniteInversion.R_four_eq_fermat p hp)
  simpa only [WPFiniteNC122.q, ← WPFiniteField.R_castHom, map_ofNat, map_neg,
    map_sub, map_mul, map_pow, map_intCast] using h

private theorem actual_ell_sixteen (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.ell p (16 : K) =
      15 * (WPFiniteJNormalization.r p + (WPFiniteInversion.integerFermatQuotient p 5 : K)) -
        64 * WPFiniteNC122.q p := by
  simpa only [finiteLogValue, WPFiniteField.ell, WPFiniteJNormalization.r, WPFiniteNC122.q]
    using (finiteLog_c_ordered (K := K) p hp).2

/-- This finite consumer contains the actual five entire summands; its joint source attachment
still retains the separately displayed original low-density and proper-product terms. -/
noncomputable def actualFiniteB2 (p : ℕ) [Fact p.Prime] [CharP K p] (u w : K) : K :=
  vbalMomentConsumer p u w + originalUVFiniteRemainder p u + normalizedZFiniteValue p u +
    NativeScalarRows.actualGKQ p +
    originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p))

/-- The original finite B2 alphabet follows from actual C3 and the actual GKQ/J source identities.
No numerical residue, free scalar assignment, invisible-slot deletion, or C1 premise is used. -/
theorem actual_finite_B2_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    actualFiniteB2 p u w = finiteB2Alphabet p u := by
  have hc3 := actual_C3_equation p hp u w hu hw
  rw [actualFiniteB2, actual_normalized_Z_HPJ p hp u hu,
    NativeScalarRows.actual_GKQ_corrected_value p hp u hu, actual_h0J_UV_split p hp u hu]
  dsimp only [vbalMomentConsumer, vbalProduct, originalUVFiniteRemainder, normalizedZWithoutH,
    finiteB2Alphabet]
  simp only [actual_UV_D_difference p hp u hu, actual_UV_even_endpoint p hp u hu,
    actual_R_four p hp, actual_ell_sixteen p hp,
    WPFiniteFifthSourceContraction.actual_a0_fifth p hp u hu,
    WPFiniteFifthSourceContraction.actual_UJ_fifth p hp u hu]
  have hT0 : -(11 / 5 : K) * u = WPFiniteNC122.T0 u := by
    unfold WPFiniteNC122.T0
    ring
  rw [hT0]
  dsimp only [mixedJQuadratic, WPFiniteNC122.h, WPFiniteNC122.q,
    WPFiniteJNormalization.r, WPFiniteFifthSourceContraction.k] at hc3 ⊢
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero 2 h2
  have h8 : (8 : K) ≠ 0 := by
    rw [show (8 : K) = 2 ^ 3 by ring]
    exact pow_ne_zero 3 h2
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h30 : (30 : K) ≠ 0 := by
    rw [show (30 : K) = 2 * 15 by ring]
    exact mul_ne_zero h2 h15
  have h40 : (40 : K) ≠ 0 := by
    rw [show (40 : K) = 8 * 5 by ring]
    exact mul_ne_zero h8 h5
  have h50 : (50 : K) ≠ 0 := by
    rw [show (50 : K) = 2 * 25 by ring]
    exact mul_ne_zero h2 h25
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 25 by ring]
    exact mul_ne_zero h3 h25
  have h100 : (100 : K) ≠ 0 := by
    rw [show (100 : K) = 4 * 25 by ring]
    exact mul_ne_zero h4 h25
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have h150 : (150 : K) ≠ 0 := by
    rw [show (150 : K) = 2 * 75 by ring]
    exact mul_ne_zero h2 h75
  have h375 : (375 : K) ≠ 0 := by
    rw [show (375 : K) = 3 * 125 by ring]
    exact mul_ne_zero h3 h125
  have h500 : (500 : K) ≠ 0 := by
    rw [show (500 : K) = 4 * 125 by ring]
    exact mul_ne_zero h4 h125
  linear_combination (norm := (field_simp [h2, h3, h4, h5, h8, h10, h15, h25, h30,
    h40, h50, h75, h100, h125, h150, h375, h500]; ring)) hc3

end WPFieldAssembly.NativeJointSuccessorB2Finite
