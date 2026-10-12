import Mathlib.Tactic

namespace WPFieldAssembly.NativeJointSuccessorFiniteCoefficientIdentity

variable {K : Type*} [Field K]

/-- Exact coefficient collection used only after the actual B2, GB, G2 and P
source identities. The harmonic letter is expanded as -2*q-3*r/2. -/
theorem whole_finite_coefficient_identity
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : (5 : K) ≠ 0)
    (q r k c loop ke g5 rm2 r16 : K) :
    (77 * loop / 75 + 22 * ke / 5 - 11 * g5 / 30 -
      5056 * q ^ 2 / 375 + 204 * q * r / 25 + 104 * q * k / 25 -
      153 * r * k / 25 - 399 * r ^ 2 / 500 + 3 * k ^ 2 / 4 +
      5434 * q * c / 375 - 341 * r * c / 125 - 319 * c ^ 2 / 75 -
      11 * rm2 / 15 - 11 * r16 / 150) +
      (287 / 600 : K) * (-2 * q - 3 * r / 2) ^ 2 +
      (-g5 / 20 + rm2 / 10 + 7 * r16 / 15 + 313 * q ^ 2 / 3 -
        27 * q * r / 10 - 13 * q * k - 15 * r * k / 2 -
        15 * k ^ 2 / 4 + 2 * q * c / 5 + 3 * r * c / 10) +
      (5 * g5 / 12 - 5 * rm2 / 6 - r16 / 20 - 193 * q ^ 2 / 50 -
        9 * q * r / 100 - 177 * r ^ 2 / 800 + 4 * q * k +
        11 * c ^ 2 / 15 - 10 * q * c / 3 - 5 * r * c / 2) -
      (1019 / 750 : K) * (-2 * q - 3 * r / 2) ^ 2 -
      ((304 / 3 : K) * q ^ 2 - 11 * q * r - 11 * q * k -
        9 * r * k - 3 * r ^ 2 - 3 * k ^ 2 + (5 / 12 : K) * r16) =
      77 * loop / 75 + 22 * ke / 5 - 2233 * q ^ 2 / 125 +
        1386 * q * r / 125 + 154 * q * k / 25 - 231 * r * k / 50 +
        4334 * q * c / 375 - 616 * r * c / 125 - 88 * c ^ 2 / 25 -
        22 * rm2 / 15 - 11 * r16 / 150 := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 ^ 2 by ring]
    exact pow_ne_zero 2 h2
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by ring]
    exact mul_ne_zero h2 h3
  have h10 : (10 : K) ≠ 0 := by
    rw [show (10 : K) = 2 * 5 by ring]
    exact mul_ne_zero h2 h5
  have h12 : (12 : K) ≠ 0 := by
    rw [show (12 : K) = 2 ^ 2 * 3 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) h3
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3 * 5 by ring]
    exact mul_ne_zero h3 h5
  have h20 : (20 : K) ≠ 0 := by
    rw [show (20 : K) = 2 ^ 2 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) h5
  have h25 : (25 : K) ≠ 0 := by
    rw [show (25 : K) = 5 ^ 2 by ring]
    exact pow_ne_zero 2 h5
  have h30 : (30 : K) ≠ 0 := by
    rw [show (30 : K) = 2 * 3 * 5 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h3) h5
  have h50 : (50 : K) ≠ 0 := by
    rw [show (50 : K) = 2 * 5 ^ 2 by ring]
    exact mul_ne_zero h2 (pow_ne_zero 2 h5)
  have h75 : (75 : K) ≠ 0 := by
    rw [show (75 : K) = 3 * 5 ^ 2 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 2 h5)
  have h100 : (100 : K) ≠ 0 := by
    rw [show (100 : K) = 2 ^ 2 * 5 ^ 2 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h5)
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero 3 h5
  have h150 : (150 : K) ≠ 0 := by
    rw [show (150 : K) = 2 * 3 * 5 ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero 2 h5)
  have h375 : (375 : K) ≠ 0 := by
    rw [show (375 : K) = 3 * 5 ^ 3 by ring]
    exact mul_ne_zero h3 (pow_ne_zero 3 h5)
  have h500 : (500 : K) ≠ 0 := by
    rw [show (500 : K) = 2 ^ 2 * 5 ^ 3 by ring]
    exact mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 3 h5)
  have h600 : (600 : K) ≠ 0 := by
    rw [show (600 : K) = 2 ^ 3 * 3 * 5 ^ 2 by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h2) h3) (pow_ne_zero 2 h5)
  have h750 : (750 : K) ≠ 0 := by
    rw [show (750 : K) = 2 * 3 * 5 ^ 3 by ring]
    exact mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero 3 h5)
  have h800 : (800 : K) ≠ 0 := by
    rw [show (800 : K) = 2 ^ 5 * 5 ^ 2 by ring]
    exact mul_ne_zero (pow_ne_zero 5 h2) (pow_ne_zero 2 h5)
  field_simp [h2, h3, h4, h5, h6, h10, h12, h15, h20, h25, h30,
    h50, h75, h100, h125, h150, h375, h500, h600, h750, h800]
  ring

end WPFieldAssembly.NativeJointSuccessorFiniteCoefficientIdentity
