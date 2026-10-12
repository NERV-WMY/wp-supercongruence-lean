import WPMomentPrecision.Conic.WPRationalInfinitySeries
import WPMomentPrecision.Conic.WPConicQuadraticResiduePolynomial

open scoped Polynomial PowerSeries LaurentSeries

namespace WPMomentPrecision.QuadraticResidueTransport

variable {K : Type*} [Field K]

def coverX (z : K) : K := 4 * z ^ 2 / (1 - z ^ 2) ^ 2

def coverJacobian (z : K) : K := 8 * z * (1 + z ^ 2) / (1 - z ^ 2) ^ 3

/-- Exact complete pullback of every negative nonlogarithmic monomial. -/
theorem negative_cover_normalform (z : K) (h4 : (4 : K) ≠ 0)
    (hz : z ≠ 0) (hu : 1 - z ^ 2 ≠ 0) (k : ℕ) :
    coverX z ^ (-(k : ℤ) - 2) * coverJacobian z =
      (8 / 4 ^ (k + 2)) * (1 + z ^ 2) * (1 - z ^ 2) ^ (2 * k + 1) /
        z ^ (2 * k + 3) := by
  rw [show -(k : ℤ) - 2 = -((k + 2 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]
  unfold coverX coverJacobian
  rw [div_pow, inv_div, mul_pow, ← pow_mul, ← pow_mul]
  have huPower : (1 - z ^ 2) ^ (2 * (k + 2)) =
      (1 - z ^ 2) ^ (2 * k + 1) * (1 - z ^ 2) ^ 3 := by
    rw [← pow_add]
    congr 1
  have hzPower : z ^ (2 * (k + 2)) = z ^ (2 * k + 3) * z := by
    rw [← pow_succ]
    congr 1
  rw [huPower, hzPower]
  field_simp

/-- The logarithmic monomial retains the tame ramification factor two. -/
theorem logarithmic_cover_normalform (z : K) (h4 : (4 : K) ≠ 0)
    (hz : z ≠ 0) (hu : 1 - z ^ 2 ≠ 0) :
    coverX z ^ (-1 : ℤ) * coverJacobian z = 2 / z + 4 * z / (1 - z ^ 2) := by
  simp only [zpow_neg_one, coverX, coverJacobian]
  field_simp
  ring

noncomputable def localX : K⸨X⸩ := HahnSeries.single 1 1

noncomputable def coverUnit : K⟦X⟧ := 1 - PowerSeries.X ^ 2

theorem coverUnit_origin : PowerSeries.constantCoeff (coverUnit : K⟦X⟧) = 1 := by
  simp [coverUnit]

theorem localX_ne_zero : (localX : K⸨X⸩) ≠ 0 := by
  simp [localX]

theorem coverUnit_cast : ((coverUnit : K⟦X⟧) : K⸨X⸩) = 1 - localX ^ 2 := by
  simp [coverUnit, localX, PowerSeries.coe_pow]

theorem coverUnit_ne_zero : (1 - (localX : K⸨X⸩) ^ 2) ≠ 0 := by
  rw [← coverUnit_cast]
  intro hz
  have hc := congrArg (fun f : K⸨X⸩ => f.coeff 0) hz
  simp [PowerSeries.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coverUnit_origin] at hc

/-- Exact negative-cover residue, including all characteristic-p resonant exponents. -/
theorem negative_cover_residue_zero (h4 : (4 : K) ≠ 0) (k : ℕ) :
    (coverX (localX : K⸨X⸩) ^ (-(k : ℤ) - 2) * coverJacobian localX).coeff (-1) = 0 := by
  have h4L : (4 : K⸨X⸩) ≠ 0 := by
    have hc : (HahnSeries.C (4 : K) : K⸨X⸩) = 4 := map_ofNat _ 4
    rw [← hc]
    exact HahnSeries.C_ne_zero h4
  rw [negative_cover_normalform localX h4L localX_ne_zero coverUnit_ne_zero k]
  let P : K[X] := (1 + Polynomial.X ^ 2) * (1 - Polynomial.X ^ 2) ^ (2 * k + 1)
  have hP : ((P : K⟦X⟧) : K⸨X⸩) =
      (1 + localX ^ 2) * (1 - localX ^ 2) ^ (2 * k + 1) := by
    simp [P, localX, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_sub,
      Polynomial.coe_pow, PowerSeries.coe_pow]
  have hs : (localX : K⸨X⸩) ^ (2 * k + 3) =
      HahnSeries.single ((2 * k + 3 : ℕ) : ℤ) 1 := by
    simp [localX]
  have he : (8 / 4 ^ (k + 2) : K⸨X⸩) * (1 + localX ^ 2) *
      (1 - localX ^ 2) ^ (2 * k + 1) / localX ^ (2 * k + 3) =
      HahnSeries.single (-((2 * k + 3 : ℕ) : ℤ)) (8 / 4 ^ (k + 2) : K) *
        ((P : K⟦X⟧) : K⸨X⸩) := by
    rw [mul_assoc, ← hP]
    calc
      (8 / 4 ^ (k + 2) : K⸨X⸩) * ((P : K⟦X⟧) : K⸨X⸩) /
          localX ^ (2 * k + 3) =
        ((8 / 4 ^ (k + 2) : K⸨X⸩) * (localX ^ (2 * k + 3))⁻¹) *
          ((P : K⟦X⟧) : K⸨X⸩) := by ring
      _ = _ := by
        have hc : (8 / 4 ^ (k + 2) : K⸨X⸩) =
            HahnSeries.C (8 / 4 ^ (k + 2) : K) := by
          symm
          rw [map_div₀, map_pow, map_ofNat, map_ofNat]
        rw [hs, HahnSeries.inv_single, hc, HahnSeries.C_apply,
          HahnSeries.single_mul_single]
        simp
  rw [he, HahnSeries.coeff_single_mul]
  have hi : (-1 : ℤ) - (-((2 * k + 3 : ℕ) : ℤ)) = ((2 * k + 2 : ℕ) : ℤ) := by omega
  rw [hi, PowerSeries.coeff_coe, if_neg (by omega), Int.natAbs_natCast,
    Polynomial.coeff_coe]
  rw [show P = (1 + Polynomial.X ^ 2) * (1 - Polynomial.X ^ 2) ^ (2 * k + 1) from rfl,
    WPConicQuadraticResiduePolynomial.quadratic_cover_even_middle_zero, mul_zero]

end WPMomentPrecision.QuadraticResidueTransport
