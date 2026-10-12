import WPFieldAssembly.NativeJointSuccessorFiniteAlphabet
import WPFieldAssembly.NativeClosureEndProductActual
import WPFieldAssembly.ActualBpairQuadraticTransport
import WPFieldAssembly.ActualNC77NativeAttachment
import WPFieldAssembly.NativeJointSuccessorFiniteCoefficientIdentity

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial

namespace WPFieldAssembly.NativeJointSuccessorFiniteNormalizer

open ActualBpairContraction ActualKwOrderedEndpoints ActualSimplePoleResidue
  NativeJointSuccessorB2Finite ActualThreePhase

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/- STATEMENT_FIDELITY: the alphabet below is the literal left side of the
existing WPActualFinalConsumer.actual_corrected_consumer, at scale one.
The native source cone does not import that final consumer. The coefficients
are retained from its checked source and the recorded B2 certificate.
This module only joins actual finite sources and the original arithmetic P;
it does not supply the missing whole native scalar source attachment. -/

noncomputable def correctedFiniteConsumer (p : ℕ) [Fact p.Prime] [CharP K p]
    (u : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  let c := WPFifthEntropy.C p u
  77 * (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u) / 75 +
    22 * (WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u) / 5 -
    2233 * q ^ 2 / 125 + 1386 * q * r / 125 + 154 * q * k / 25 -
    231 * r * k / 50 + 4334 * q * c / 375 - 616 * r * c / 125 -
    88 * c ^ 2 / 25 - 22 * WPFiniteField.R p (-2) / 15 -
    11 * WPFiniteField.R p 16 / 150

/-- The actual complete G2 source has its original NC126 value. -/
theorem actual_G2_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    actualNativeG2Residue (K := K) p =
      5 * originalG p (1 / 5) / 12 - 5 * WPFiniteField.R p (-2) / 6 -
        WPFiniteField.R p 16 / 20 - 193 * WPFiniteNC122.q p ^ 2 / 50 -
        9 * WPFiniteNC122.q p * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 100 -
        177 * (WPFiniteInversion.integerFermatQuotient p 3 : K) ^ 2 / 800 +
        4 * WPFiniteNC122.q p * (WPFiniteInversion.integerFermatQuotient p 5 : K) +
        11 * WPFifthEntropy.C p u ^ 2 / 15 -
        10 * WPFiniteNC122.q p * WPFifthEntropy.C p u / 3 -
        5 * (WPFiniteInversion.integerFermatQuotient p 3 : K) * WPFifthEntropy.C p u / 2 := by
  rw [actualNativeG2Residue_full_tails p hp, actualNativeG2Tail_NC126 p hp u hu]

/-- The same arithmetic P maps from its integral rational digit, including R(16). -/
theorem actual_P_transport (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    φ (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) =
      (304 / 3 : K) * (WPFiniteInversion.integerFermatQuotient p 2 : K) ^ 2 -
        11 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
          (WPFiniteInversion.integerFermatQuotient p 3 : K) -
        11 * (WPFiniteInversion.integerFermatQuotient p 2 : K) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) -
        9 * (WPFiniteInversion.integerFermatQuotient p 3 : K) *
          (WPFiniteInversion.integerFermatQuotient p 5 : K) -
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) ^ 2 -
        3 * (WPFiniteInversion.integerFermatQuotient p 5 : K) ^ 2 +
        (5 / 12 : K) * WPFiniteField.R p 16 := by
  rw [ActualNC77NativeAttachment.actualP_field p hp]
  simp only [map_add, map_sub, map_mul, map_pow, map_div₀, map_ofNat, map_intCast]
  have hf : φ (K := K) p = ZMod.castHom (dvd_refl p) K := Subsingleton.elim _ _
  rw [hf, ← WPFiniteField.R_castHom]
  simp only [map_ofNat]

/-- Finite B2, actual chi0 end product, and full G2 retain precisely the whole
corrected consumer after the original divided-Vbal and native harmonic offsets. -/
theorem actual_finite_B2_normalization (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    finiteB2Alphabet p u + (287 / 600 : K) * WPFiniteNC122.h p ^ 2 +
        endProductActualGB p u + actualNativeG2Residue p -
        (1019 / 750 : K) * WPFiniteNC122.h p ^ 2 -
        φ (K := K) p (WPMomentPrecision.MomentPrecision.actualP p : ZMod p) =
      correctedFiniteConsumer p u := by
  rw [endProduct_actual_GB_value p hp u hu, actual_G2_value p hp u hu,
    actual_P_transport p hp]
  dsimp only [finiteB2Alphabet, correctedFiniteConsumer, WPFiniteNC122.h,
    WPFiniteNC122.q, ActualRationalSignRows.q3]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  exact NativeJointSuccessorFiniteCoefficientIdentity.whole_finite_coefficient_identity
    h2 h3 h5
    (WPFiniteInversion.integerFermatQuotient p 2 : K)
    (WPFiniteInversion.integerFermatQuotient p 3 : K)
    (WPFiniteInversion.integerFermatQuotient p 5 : K) (WPFifthEntropy.C p u)
    (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u)
    (WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u)
    (originalG p (1 / 5)) (WPFiniteField.R p (-2)) (WPFiniteField.R p 16)

end WPFieldAssembly.NativeJointSuccessorFiniteNormalizer
