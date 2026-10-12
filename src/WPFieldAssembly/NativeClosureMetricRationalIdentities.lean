import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace WPFieldAssembly.NativeClosureMetricRationalIdentities

variable {K : Type*} [Field K]

/-- The two full reciprocal Euler coefficients collect to 25/18. -/
theorem euler_reciprocal_coefficient (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (5 / 24 : K) * 4 + 5 / 9 = 25 / 18 := by
  have h9 : (9 : K) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1; norm_num
  have h18 : (18 : K) ≠ 0 := by
    convert mul_ne_zero h2 h9 using 1; norm_num
  have h24 : (24 : K) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) h3 using 1; norm_num
  field_simp [h9, h18, h24]
  ring

/-- The two thirds retain the original ninth coefficient. -/
theorem third_square_coefficient (h3 : (3 : K) ≠ 0) :
    (1 / 3 : K) * (1 / 3) = 1 / 9 := by
  have h9 : (9 : K) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1; norm_num
  field_simp [h3, h9]
  ring

/-- The original third and half retain the sixth coefficient. -/
theorem third_half_coefficient (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (1 / 3 : K) * (1 / 2) = 1 / 6 := by
  have h6 : (6 : K) ≠ 0 := by
    convert mul_ne_zero h2 h3 using 1; norm_num
  field_simp [h2, h3, h6]
  ring

/-- The complete conic and metric Gauss values collect at their common scale. -/
theorem joint_gauss_coefficient (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (h5 : (5 : K) ≠ 0) (y : K) :
    -(6 / 125 : K) * y ^ 2 - (1177 / 750 : K) * y ^ 2 =
      -(1213 / 750 : K) * y ^ 2 := by
  have h125 : (125 : K) ≠ 0 := by
    convert pow_ne_zero 3 h5 using 1; norm_num
  have h750 : (750 : K) ≠ 0 := by
    convert mul_ne_zero h2 (mul_ne_zero h3 h125) using 1; norm_num
  field_simp [h125, h750]
  ring

end WPFieldAssembly.NativeClosureMetricRationalIdentities
