import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace WPFinalEndpointAlgebra

private theorem fixed_denominator_nonzero (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (n : ℕ) (hn : n ∣ 2 ^ 8 * 3 ^ 3 * 5 ^ 5) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  have hprime : p.Prime := Fact.out
  have hnzero : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
  have hproduct := dvd_trans hnzero hn
  rcases hprime.dvd_mul.mp hproduct with h23 | h5
  · rcases hprime.dvd_mul.mp h23 with h2 | h3
    · have hp2 := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2)
      omega
    · have hp3 := Nat.le_of_dvd (by decide : 0 < 3) (hprime.dvd_of_dvd_pow h3)
      omega
  · have hp5 := Nat.le_of_dvd (by decide : 0 < 5) (hprime.dvd_of_dvd_pow h5)
    omega

/-- Expand the original source before harmonic or endpoint substitution. -/
theorem original_source_constant (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (a h q A tj : ZMod p) :
    -2 * (-A + q ^ 2 / 2 + (a + h) ^ 2 / 6 + tj / 3 +
      (2 * h / 3 - q) * (a + h)) - a ^ 2 + h ^ 2 =
      2 * A - 4 * a ^ 2 / 3 + 2 * (q - h) * a -
        2 * h ^ 2 / 3 + 2 * q * h - q ^ 2 - 2 * tj / 3 := by
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd3 : (3 : ZMod p) = d3
  generalize hd6 : (6 : ZMod p) = d6
  have h2 : d2 ≠ 0 := hd2 ▸ fixed_denominator_nonzero p hp 2 (by norm_num)
  have h3 : d3 ≠ 0 := hd3 ▸ fixed_denominator_nonzero p hp 3 (by norm_num)
  have h6 : d6 ≠ 0 := hd6 ▸ fixed_denominator_nonzero p hp 6 (by norm_num)
  field_simp [h2, h3, h6]
  subst d2 d3 d6
  ring

/-- The repaired constant is forced by the literal harmonic relation. -/
theorem source_constant_correction (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q r : ZMod p) :
    2 * q * (-2 * q - 3 * r / 2) -
        4 * (-2 * q - 3 * r / 2) ^ 2 / 3 =
      -28 * q ^ 2 / 3 - 11 * q * r - 3 * r ^ 2 := by
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd3 : (3 : ZMod p) = d3
  have h2 : d2 ≠ 0 := hd2 ▸ fixed_denominator_nonzero p hp 2 (by norm_num)
  have h3 : d3 ≠ 0 := hd3 ▸ fixed_denominator_nonzero p hp 3 (by norm_num)
  field_simp [h2, h3]
  subst d2 d3
  ring

/-- Eliminate the retained fifth value only from the proved rational rows. -/
theorem rational_weight_two_relation (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q k rm2 r4 rm4 r5 r16 : ZMod p)
    (h4 : r4 = -6 * q ^ 2 - 2 * rm2)
    (hmirror : -4 * rm4 + 5 * r5 = -(8 * q - 5 * k) ^ 2 / 2)
    (h16 : r16 = 10 * r4 - 6 * rm4) :
    r16 + 20 * rm2 + 15 * r5 / 2 =
      -108 * q ^ 2 + 60 * q * k - 75 * k ^ 2 / 4 := by
  have hrm4 : rm4 = (5 * r5 + (8 * q - 5 * k) ^ 2 / 2) / 4 := by
    apply (eq_div_iff (fixed_denominator_nonzero p hp 4 (by norm_num))).mpr
    linear_combination -hmirror
  rw [h16, h4, hrm4]
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd4 : (4 : ZMod p) = d4
  have h2 : d2 ≠ 0 := hd2 ▸ fixed_denominator_nonzero p hp 2 (by norm_num)
  have h4den : d4 ≠ 0 := hd4 ▸ fixed_denominator_nonzero p hp 4 (by norm_num)
  field_simp [h2, h4den]
  subst d2 d4
  ring

/-- Convert the actual endpoint while retaining the original R(5) input. -/
theorem real_endpoint_elimination (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q k C rm2 r5 r16 : ZMod p)
    (hrel : r16 + 20 * rm2 + 15 * r5 / 2 =
      -108 * q ^ 2 + 60 * q * k - 75 * k ^ 2 / 4) :
    -r5 / 8 - 5 * k ^ 2 / 16 + q * k - 11 * q ^ 2 / 10 -
        q * C / 5 + 4 * C ^ 2 / 5 =
      7 * q ^ 2 / 10 - q * C / 5 + 4 * C ^ 2 / 5 + rm2 / 3 + r16 / 60 := by
  have hr16 : r16 = -108 * q ^ 2 + 60 * q * k - 75 * k ^ 2 / 4 -
      20 * rm2 - 15 * r5 / 2 := by
    linear_combination hrel
  rw [hr16]
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd3 : (3 : ZMod p) = d3
  generalize hd4 : (4 : ZMod p) = d4
  generalize hd5 : (5 : ZMod p) = d5
  generalize hd8 : (8 : ZMod p) = d8
  generalize hd10 : (10 : ZMod p) = d10
  generalize hd16 : (16 : ZMod p) = d16
  generalize hd60 : (60 : ZMod p) = d60
  have h2 : d2 ≠ 0 := hd2 ▸ fixed_denominator_nonzero p hp 2 (by norm_num)
  have h3 : d3 ≠ 0 := hd3 ▸ fixed_denominator_nonzero p hp 3 (by norm_num)
  have h4den : d4 ≠ 0 := hd4 ▸ fixed_denominator_nonzero p hp 4 (by norm_num)
  have h5 : d5 ≠ 0 := hd5 ▸ fixed_denominator_nonzero p hp 5 (by norm_num)
  have h8 : d8 ≠ 0 := hd8 ▸ fixed_denominator_nonzero p hp 8 (by norm_num)
  have h10 : d10 ≠ 0 := hd10 ▸ fixed_denominator_nonzero p hp 10 (by norm_num)
  have h16den : d16 ≠ 0 := hd16 ▸ fixed_denominator_nonzero p hp 16 (by norm_num)
  have h60 : d60 ≠ 0 := hd60 ▸ fixed_denominator_nonzero p hp 60 (by norm_num)
  field_simp [h2, h3, h4den, h5, h8, h10, h16den, h60]
  subst d2 d3 d4 d5 d8 d10 d16 d60
  ring

/-- The corrected original consumer cancels with the full loop and actual end. -/
theorem corrected_final_consumer (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (q r k C rm2 r16 loop kend : ZMod p)
    (hloop : loop = -6 * q * k + 9 * r * k / 2 + 72 * q ^ 2 / 5 -
      54 * q * r / 5 - 52 * q * C / 5 + 24 * r * C / 5)
    (hend : kend = 7 * q ^ 2 / 10 - q * C / 5 + 4 * C ^ 2 / 5 +
      rm2 / 3 + r16 / 60) :
    77 * loop / 75 + 22 * kend / 5 - 2233 * q ^ 2 / 125 +
      1386 * q * r / 125 + 154 * q * k / 25 - 231 * r * k / 50 +
      4334 * q * C / 375 - 616 * r * C / 125 - 88 * C ^ 2 / 25 -
      22 * rm2 / 15 - 11 * r16 / 150 = 0 := by
  rw [hloop, hend]
  generalize hd2 : (2 : ZMod p) = d2
  generalize hd3 : (3 : ZMod p) = d3
  generalize hd5 : (5 : ZMod p) = d5
  generalize hd10 : (10 : ZMod p) = d10
  generalize hd15 : (15 : ZMod p) = d15
  generalize hd25 : (25 : ZMod p) = d25
  generalize hd50 : (50 : ZMod p) = d50
  generalize hd60 : (60 : ZMod p) = d60
  generalize hd75 : (75 : ZMod p) = d75
  generalize hd125 : (125 : ZMod p) = d125
  generalize hd150 : (150 : ZMod p) = d150
  generalize hd375 : (375 : ZMod p) = d375
  have h2 : d2 ≠ 0 := hd2 ▸ fixed_denominator_nonzero p hp 2 (by norm_num)
  have h3 : d3 ≠ 0 := hd3 ▸ fixed_denominator_nonzero p hp 3 (by norm_num)
  have h5 : d5 ≠ 0 := hd5 ▸ fixed_denominator_nonzero p hp 5 (by norm_num)
  have h10 : d10 ≠ 0 := hd10 ▸ fixed_denominator_nonzero p hp 10 (by norm_num)
  have h15 : d15 ≠ 0 := hd15 ▸ fixed_denominator_nonzero p hp 15 (by norm_num)
  have h25 : d25 ≠ 0 := hd25 ▸ fixed_denominator_nonzero p hp 25 (by norm_num)
  have h50 : d50 ≠ 0 := hd50 ▸ fixed_denominator_nonzero p hp 50 (by norm_num)
  have h60 : d60 ≠ 0 := hd60 ▸ fixed_denominator_nonzero p hp 60 (by norm_num)
  have h75 : d75 ≠ 0 := hd75 ▸ fixed_denominator_nonzero p hp 75 (by norm_num)
  have h125 : d125 ≠ 0 := hd125 ▸ fixed_denominator_nonzero p hp 125 (by norm_num)
  have h150 : d150 ≠ 0 := hd150 ▸ fixed_denominator_nonzero p hp 150 (by norm_num)
  have h375 : d375 ≠ 0 := hd375 ▸ fixed_denominator_nonzero p hp 375 (by norm_num)
  field_simp [h2, h3, h5, h10, h15, h25, h50, h60, h75, h125, h150, h375]
  subst d2 d3 d5 d10 d15 d25 d50 d60 d75 d125 d150 d375
  ring

end WPFinalEndpointAlgebra
