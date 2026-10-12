import WPFieldAssembly.NativeJointSuccessorJrawCollected

open scoped Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorC3

open ActualBpairContraction ActualCubicNativeSource ActualSimplePoleResidue
open ActualRationalSignRows ActualKwOrderedEndpoints ActualVbalFieldClosure
open NativeClosureMixedSource NativeClosureMixedJ
open NativeJointSuccessorJrawCollected

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The original C2 quadratic, kept literally for the final joint B2 collection. -/
noncomputable def mixedJQuadratic (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let q := WPFiniteNC122.q (K := K) p
  let h := WPFiniteNC122.h (K := K) p
  let C := WPFifthEntropy.C p u
  let k : K := WPFiniteInversion.integerFermatQuotient p 5;
  -(2 / 25 : K) * q ^ 2 + (176 / 75 : K) * h * q - (313 / 375 : K) * h ^ 2 -
    (62 / 25 : K) * q * C - (149 / 75 : K) * C ^ 2 - (88 / 15 : K) * h * C -
    (44 / 5 : K) * (q - C) * k - (11 / 10 : K) * h * k

/-- The actual whole Jraw source is added to the unchanged six ordered HPJ rows.
The only hypotheses are the original prime, characteristic, and genuine root data. -/
theorem actual_C3_H_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    HPJRow (K := K) p +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) -
        (11 / 15 : K) * conicPacket p u w =
      -(11 / 10 : K) * originalG p (1 / 5) +
        (77 / 75 : K) * (WPFiniteDReciprocity.Bt p u - WPFiniteDReciprocity.At p u) -
        (8 / 25 : K) * (q2 (K := K) p - 3 * q3 p / 4) ^ 2 + mixedJProduct p u := by
  rw [actual_Jraw_collected_value p hp u w hu hw]
  calc
    _ = -(11 / 10 : K) * originalG p (1 / 5) +
        (HPJRow (K := K) p + mixedJHRow p) + mixedJProduct p u := by ring
    _ = _ := by rw [actual_HPJ_mixedJ_H_collection p hp u hu]; ring

/-- The original definition h=-2q-3r/2 changes the collected product to the C2 quadratic.
The shared C and Q5 terms cancel literally; no residue or scalar-value premise is used. -/
theorem actual_C3_product_collection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    mixedJProduct p u - (8 / 25 : K) * (q2 (K := K) p - 3 * q3 p / 4) ^ 2 =
      (373 / 75 : K) * WPFiniteNC122.q p ^ 2 -
        (34 / 5 : K) * WPFiniteNC122.q p * WPFiniteJNormalization.r p +
        (72 / 25 : K) * WPFiniteJNormalization.r p ^ 2 + mixedJQuadratic p u := by
  dsimp only [mixedJProduct, mixedJQuadratic, WPFiniteNC122.h, WPFiniteNC122.q,
    WPFiniteJNormalization.r, q2, q3]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero 2 h2
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 25 by ring]
    exact mul_ne_zero h3 h25
  have h375 : (375 : K) ≠ 0 := by
    rw [show (375 : K) = 3 * 5 ^ 3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 3 h5)
  field_simp [h2, h3, h4, h5, h10, h15, h25, h75, h375]
  ring

/-- The original C3 equation follows from the actual Jraw source and reviewed H dictionary.
This preserves the full mixedJNumerator, its origin pole, and both original square-root phases. -/
theorem actual_C3_equation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    HPJRow (K := K) p +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) -
        (11 / 15 : K) * conicPacket p u w =
      -(11 / 10 : K) * originalG p (1 / 5) +
        (77 / 75 : K) * (WPFiniteDReciprocity.Bt p u - WPFiniteDReciprocity.At p u) +
        (373 / 75 : K) * WPFiniteNC122.q p ^ 2 -
        (34 / 5 : K) * WPFiniteNC122.q p * WPFiniteJNormalization.r p +
        (72 / 25 : K) * WPFiniteJNormalization.r p ^ 2 + mixedJQuadratic p u := by
  rw [actual_C3_H_collection p hp u w hu hw]
  calc
    _ = -(11 / 10 : K) * originalG p (1 / 5) +
        (77 / 75 : K) * (WPFiniteDReciprocity.Bt p u - WPFiniteDReciprocity.At p u) +
        (mixedJProduct p u - (8 / 25 : K) * (q2 (K := K) p - 3 * q3 p / 4) ^ 2) := by ring
    _ = _ := by rw [actual_C3_product_collection p hp u]; ring

/-- The complete literal C3 scalar keeps every original C2 product coefficient visible. -/
theorem actual_C3_expanded_equation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u w : K) (hu : u ^ 2 = 1 / 5) (hw : w ^ 2 = 3 / 11) :
    HPJRow (K := K) p +
        originPole (mixedJNumerator p (actualAK p : K[X]).toLaurent (WPFiniteNC122.h p)) -
        (11 / 15 : K) * conicPacket p u w =
      -(11 / 10 : K) * originalG p (1 / 5) +
        (77 / 75 : K) * (WPFiniteDReciprocity.Bt p u - WPFiniteDReciprocity.At p u) +
        (373 / 75 : K) * WPFiniteNC122.q p ^ 2 -
        (34 / 5 : K) * WPFiniteNC122.q p * WPFiniteJNormalization.r p +
        (72 / 25 : K) * WPFiniteJNormalization.r p ^ 2 -
        (2 / 25 : K) * WPFiniteNC122.q p ^ 2 +
        (176 / 75 : K) * WPFiniteNC122.h p * WPFiniteNC122.q p -
        (313 / 375 : K) * WPFiniteNC122.h p ^ 2 -
        (62 / 25 : K) * WPFiniteNC122.q p * WPFifthEntropy.C p u -
        (149 / 75 : K) * WPFifthEntropy.C p u ^ 2 -
        (88 / 15 : K) * WPFiniteNC122.h p * WPFifthEntropy.C p u -
        (44 / 5 : K) * (WPFiniteNC122.q p - WPFifthEntropy.C p u) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) -
        (11 / 10 : K) * WPFiniteNC122.h p *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) := by
  rw [actual_C3_equation p hp u w hu hw]
  dsimp only [mixedJQuadratic]
  ring

end WPFieldAssembly.NativeJointSuccessorC3
