import WPActualFinalConsumer
import WPFieldAssembly.ActualNC77NativeAttachment
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WPFieldAssembly.ActualScalarClosure

open scoped Polynomial
open Polynomial WPFieldAssembly.NativeOriginalResidues

namespace WPFieldAssembly.AllPrimesLiteral

set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

/-- The same faithful field contains both conic coordinates used by the actual sources. -/
theorem exists_joint_faithful_coordinates (p : ℕ) [Fact p.Prime] :
    ∃ u w : AlgebraicClosure (ZMod p), u ^ 2 = 1 / 5 ∧ w ^ 2 = 3 / 11 := by
  obtain ⟨u, hu⟩ := ActualScalarClosure.exists_faithful_fifth_coordinate p
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq
    (3 / 11 : AlgebraicClosure (ZMod p)) (by norm_num : 0 < (2 : ℕ))
  exact ⟨u, w, hu, hw⟩

/-- Mapping the complete canceled density preserves every coefficient band. -/
theorem canceledDensity_map {F : Type*} [Field F] (f : K →+* F) (P : K[X]) :
    (WPFiniteNC122Residue.canceledDensity P).map f =
      WPFiniteNC122Residue.canceledDensity (P.map f) := by
  simp only [WPFiniteNC122Residue.canceledDensity, Polynomial.map_mul,
    Polynomial.map_comp, divX_map_local, WPFiniteNC122Residue.Qrev,
    WPFiniteNC122Residue.Frev, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    _root_.map_div₀, _root_.map_ofNat]

/-- All original p-shifted projections commute with faithful field extension. -/
theorem original_projection_map {F : Type*} [Field F]
    (f : K →+* F) (p j : ℕ) (P : K[X]) :
    f (WPFieldAssembly.ResidualProjection.Ij p j P) =
      WPFieldAssembly.ResidualProjection.Ij p j (P.map f) := by
  simp only [WPFieldAssembly.ResidualProjection.Ij, ← canceledDensity_map f P,
    Polynomial.coeff_map]

/-- The mapped original norm retains both quadratic projections at their original weights. -/
theorem original_norm_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ZMod.castHom (dvd_refl p) K (originalNorm p : ZMod p) =
      12 * WPFieldAssembly.ResidualProjection.Ij p 0
        (((WPFieldAssembly.ActualNC77Chart.integralNormQ p (by omega)).map
          (WPPIntegralReduction.residueHom p)).map (ZMod.castHom (dvd_refl p) K)) +
      (15 / 2 : K) * WPFieldAssembly.ResidualProjection.Ij p 1
        (((WPFieldAssembly.ActualNC77Chart.integralNormQ p (by omega)).map
          (WPPIntegralReduction.residueHom p)).map (ZMod.castHom (dvd_refl p) K)) := by
  rw [original_norm_field p hp]
  simp only [_root_.map_add, _root_.map_mul, _root_.map_div₀,
    _root_.map_ofNat, original_projection_map]

private theorem smooth_denominator_ne_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (n : ℕ) (hn : n ∣ 2 ^ 8 * 3 ^ 3 * 5 ^ 5) :
    (n : K) ≠ 0 := by
  intro hz
  have hprime : p.Prime := Fact.out
  have hproduct := dvd_trans ((CharP.cast_eq_zero_iff K p n).mp hz) hn
  rcases hprime.dvd_mul.mp hproduct with h23 | h5
  · rcases hprime.dvd_mul.mp h23 with h2 | h3
    · have hp2 := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2)
      omega
    · have hp3 := Nat.le_of_dvd (by decide : 0 < 3) (hprime.dvd_of_dvd_pow h3)
      omega
  · have hp5 := Nat.le_of_dvd (by decide : 0 < 5) (hprime.dvd_of_dvd_pow h5)
    omega

/-- Complete packet subtraction at scale one, before any actual-source instantiation. -/
theorem whole_packet_subtraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (q r k c rm2 r16 loop ke g5 : K) :
    (77 * loop / 75 + 22 * ke / 5 - 11 * g5 / 30 -
      5056 * q ^ 2 / 375 + 204 * q * r / 25 + 104 * q * k / 25 -
      153 * r * k / 25 - 399 * r ^ 2 / 500 + 3 * k ^ 2 / 4 +
      5434 * q * c / 375 - 341 * r * c / 125 - 319 * c ^ 2 / 75 -
      11 * rm2 / 15 - 11 * r16 / 150) +
    (11 * g5 / 30 - 11 * rm2 / 15 + 5 * r16 / 12 +
      15071 * q ^ 2 / 150 - 279 * q * r / 100 - 177 * r ^ 2 / 800 -
      9 * q * k - 15 * r * k / 2 - 15 * k ^ 2 / 4 -
      44 * q * c / 15 - 11 * r * c / 5 + 11 * c ^ 2 / 15) +
    (287 / 600 - 1019 / 750) * (-2 * q - 3 * r / 2) ^ 2 -
    (304 * q ^ 2 / 3 - 11 * q * r - 11 * q * k - 9 * r * k -
      3 * r ^ 2 - 3 * k ^ 2 + 5 * r16 / 12) =
    77 * loop / 75 + 22 * ke / 5 - 2233 * q ^ 2 / 125 +
      1386 * q * r / 125 + 154 * q * k / 25 - 231 * r * k / 50 +
      4334 * q * c / 375 - 616 * r * c / 125 - 88 * c ^ 2 / 25 -
      22 * rm2 / 15 - 11 * r16 / 150 := by
  generalize hd2 : (2 : K) = d2
  generalize hd3 : (3 : K) = d3
  generalize hd4 : (4 : K) = d4
  generalize hd5 : (5 : K) = d5
  generalize hd12 : (12 : K) = d12
  generalize hd15 : (15 : K) = d15
  generalize hd25 : (25 : K) = d25
  generalize hd30 : (30 : K) = d30
  generalize hd50 : (50 : K) = d50
  generalize hd75 : (75 : K) = d75
  generalize hd100 : (100 : K) = d100
  generalize hd125 : (125 : K) = d125
  generalize hd150 : (150 : K) = d150
  generalize hd375 : (375 : K) = d375
  generalize hd500 : (500 : K) = d500
  generalize hd600 : (600 : K) = d600
  generalize hd750 : (750 : K) = d750
  generalize hd800 : (800 : K) = d800
  have h2 : d2 ≠ 0 := hd2 ▸ smooth_denominator_ne_zero (K := K) p hp 2 (by norm_num)
  have h3 : d3 ≠ 0 := hd3 ▸ smooth_denominator_ne_zero (K := K) p hp 3 (by norm_num)
  have h4 : d4 ≠ 0 := hd4 ▸ smooth_denominator_ne_zero (K := K) p hp 4 (by norm_num)
  have h5 : d5 ≠ 0 := hd5 ▸ smooth_denominator_ne_zero (K := K) p hp 5 (by norm_num)
  have h12 : d12 ≠ 0 := hd12 ▸ smooth_denominator_ne_zero (K := K) p hp 12 (by norm_num)
  have h15 : d15 ≠ 0 := hd15 ▸ smooth_denominator_ne_zero (K := K) p hp 15 (by norm_num)
  have h25 : d25 ≠ 0 := hd25 ▸ smooth_denominator_ne_zero (K := K) p hp 25 (by norm_num)
  have h30 : d30 ≠ 0 := hd30 ▸ smooth_denominator_ne_zero (K := K) p hp 30 (by norm_num)
  have h50 : d50 ≠ 0 := hd50 ▸ smooth_denominator_ne_zero (K := K) p hp 50 (by norm_num)
  have h75 : d75 ≠ 0 := hd75 ▸ smooth_denominator_ne_zero (K := K) p hp 75 (by norm_num)
  have h100 : d100 ≠ 0 := hd100 ▸ smooth_denominator_ne_zero (K := K) p hp 100 (by norm_num)
  have h125 : d125 ≠ 0 := hd125 ▸ smooth_denominator_ne_zero (K := K) p hp 125 (by norm_num)
  have h150 : d150 ≠ 0 := hd150 ▸ smooth_denominator_ne_zero (K := K) p hp 150 (by norm_num)
  have h375 : d375 ≠ 0 := hd375 ▸ smooth_denominator_ne_zero (K := K) p hp 375 (by norm_num)
  have h500 : d500 ≠ 0 := hd500 ▸ smooth_denominator_ne_zero (K := K) p hp 500 (by norm_num)
  have h600 : d600 ≠ 0 := hd600 ▸ smooth_denominator_ne_zero (K := K) p hp 600 (by norm_num)
  have h750 : d750 ≠ 0 := hd750 ▸ smooth_denominator_ne_zero (K := K) p hp 750 (by norm_num)
  have h800 : d800 ≠ 0 := hd800 ▸ smooth_denominator_ne_zero (K := K) p hp 800 (by norm_num)
  field_simp [h2, h3, h4, h5, h12, h15, h25, h30, h50, h75, h100,
    h125, h150, h375, h500, h600, h750, h800]
  subst d2 d3 d4 d5 d12 d15 d25 d30 d50 d75 d100 d125 d150 d375 d500 d600 d750 d800
  ring

/-- The complete explicit finite B2 alphabet; its actual source identification is separate. -/
noncomputable def finiteB2 (p : ℕ) [Fact p.Prime] [CharP K p] (u g5 : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  let c := WPFifthEntropy.C p u
  let loop := WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u
  let ke := WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u
  77 * loop / 75 + 22 * ke / 5 - 11 * g5 / 30 -
    5056 * q ^ 2 / 375 + 204 * q * r / 25 + 104 * q * k / 25 -
    153 * r * k / 25 - 399 * r ^ 2 / 500 + 3 * k ^ 2 / 4 +
    5434 * q * c / 375 - 341 * r * c / 125 - 319 * c ^ 2 / 75 -
    11 * WPFiniteField.R p (-2) / 15 - 11 * WPFiniteField.R p 16 / 150

/-- The complementary explicit native finite alphabet keeps the same fifth carrier. -/
noncomputable def finiteGBG2 (p : ℕ) [Fact p.Prime] [CharP K p] (u g5 : K) : K :=
  let q : K := WPFiniteInversion.integerFermatQuotient p 2
  let r : K := WPFiniteInversion.integerFermatQuotient p 3
  let k : K := WPFiniteInversion.integerFermatQuotient p 5
  let c := WPFifthEntropy.C p u
  11 * g5 / 30 - 11 * WPFiniteField.R p (-2) / 15 + 5 * WPFiniteField.R p 16 / 12 +
    15071 * q ^ 2 / 150 - 279 * q * r / 100 - 177 * r ^ 2 / 800 -
    9 * q * k - 15 * r * k / 2 - 15 * k ^ 2 / 4 -
    44 * q * c / 15 - 11 * r * c / 5 + 11 * c ^ 2 / 15

/-- The finite expression to which the whole actual joint source must be attached. -/
noncomputable def finiteWholePacket (p : ℕ) [Fact p.Prime] [CharP K p] (u g5 : K) : K :=
  finiteB2 p u g5 + finiteGBG2 p u g5 +
    (287 / 600 - 1019 / 750) *
      (-2 * (WPFiniteInversion.integerFermatQuotient p 2 : K) -
        3 * (WPFiniteInversion.integerFermatQuotient p 3 : K) / 2) ^ 2

/-- Known finite-loop and endpoint identities evaluate the whole explicit packet for either branch. -/
theorem finite_whole_packet_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) (g5 : K) :
    finiteWholePacket p u g5 = ActualScalarClosure.originalArithmetic (K := K) p := by
  have he := whole_packet_subtraction p hp
    (WPFiniteInversion.integerFermatQuotient p 2 : K)
    (WPFiniteInversion.integerFermatQuotient p 3 : K)
    (WPFiniteInversion.integerFermatQuotient p 5 : K)
    (WPFifthEntropy.C p u) (WPFiniteField.R p (-2)) (WPFiniteField.R p 16)
    (WPFiniteLoop.A p u - WPFiniteLoop.B p u + WPFiniteLoop.Chi p u)
    (WPFiniteField.Ke p (2 * u) - WPFiniteField.Ke p u) g5
  have hz := WPActualFinalConsumer.actual_corrected_consumer p hp u hu
  apply sub_eq_zero.mp
  dsimp only [finiteWholePacket, finiteB2, finiteGBG2, ActualScalarClosure.originalArithmetic]
  convert he.trans hz using 1
  simp only [div_eq_mul_inv]
  ring

end WPFieldAssembly.AllPrimesLiteral
