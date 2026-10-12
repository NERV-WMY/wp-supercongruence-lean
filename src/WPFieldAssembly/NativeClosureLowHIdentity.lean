import WPFieldAssembly.ActualBpairLowHWholeAlgebra

namespace WPFieldAssembly.NativeClosureLowH
set_option maxHeartbeats 2400000

/-- The IR68b cancellation is a complete differential identity before endpoint extraction. -/
theorem original_Xi_reduction {F : Type*} [Field F]
    (G Xn u v P Ds Dv dU dV dP dDs dDv yl ylq φ : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (hP : P - Ds = (u - v) / 3 + φ * (Ds + Dv) / 5)
    (hDP : dP - dDs = (dU - dV) / 3 + φ * (dDs + dDv) / 5) :
    5 * G * (v * dU + (u - (1 + Xn) * v) * dV) / 12 +
        5 * G * (u * yl - Xn * v * ylq) / 24 -
        5 * G * (v * (dP - dDs) + (P - Ds) * dV) / 4 =
      5 * G * (1 - Xn) * v * dV / 12 +
        5 * G * (u * yl - Xn * v * ylq) / 24 -
        G * φ * (v * (dDs + dDv) + (Ds + Dv) * dV) / 4 := by
  rw [hP, hDP]
  have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h12 : (12 : F) ≠ 0 := by convert mul_ne_zero h4 h3 using 1; ring
  have h24 : (24 : F) ≠ 0 := by
    convert mul_ne_zero (mul_ne_zero (pow_ne_zero 3 h2) h3) one_ne_zero using 1
    ring
  field_simp [h2, h3, h4, h5, h12, h24]
  ring

/-- The entire IR66h-to-IR71c identity keeps the true derivative and reciprocal half-band. -/
theorem original_H_source_reduction {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (h5 : (5 : F) ≠ 0)
    (G Xp Xn sN u v P Pv Ds Dv dU dV dP dDs dDv yl ylq z Q y KB DK h q2 : F)
    (hGX : G * Xp = 1)
    (hP : P - Ds = (u - v) / 3 + (4 * Xp - 11) * (Ds + Dv) / 5)
    (hPv : Pv - Dv = (v - u) / 3 + (4 * G - 11) * (Ds + Dv) / 5)
    (hDP : dP - dDs = (dU - dV) / 3 + (4 * Xp - 11) * (dDs + dDv) / 5)
    (hU : dU = 3 * (4 * G - 11) * dDs / 5 - yl / 2 - 3 * (4 * G - 11) * Q / 2)
    (hV : dV = 3 * (4 * Xp - 11) * dDv / 5 - ylq / 2 + 3 * (4 * Xp - 11) * Q / 2)
    (hXnV : Xn * (2 * dV + ylq) = 3 * (4 * Xp - 11) * sN * Q)
    (hDs : dDs = 5 * (1 - sN) * Q / 2) :
    (P - u / 3) * y * DK - 5 * KB * yl / 6 +
      (5 * G * (v * dU + (u - (1 + Xn) * v) * dV) / 12 +
        5 * G * (u * yl - Xn * v * ylq) / 24 -
        5 * G * (v * (dP - dDs) + (P - Ds) * dV) / 4) -
      5 * (v - (q2 - h)) * Q / 3 - 2 * (Ds + Pv) * dV / 3 +
      2 * ((v + h) - (1 + Xn) * (u + h)) * dV / 9 -
      (u + Xn * (u + h)) * ylq / 9 - Pv * ylq / 3 -
      2 * (4 * Xp - 11) * (Ds + Dv) * (z / 2 + dU / 3) / 5 =
    ((P - u / 3) * y * DK - 5 * KB * yl / 6 +
      2 * (4 * Xp - 11) * (u + h - 3 * (4 * G - 11) * (Ds + Dv) / 5) * dDs / 15 +
      (4 * Xp - 11) * (133 * G - 12) * (Ds + Dv) * dDv / 100 -
      (15 * G + 8) * v * ylq / 72 + Ds * ylq / 3 +
      G * (4 * Xp - 11) * (Ds + Dv) * ylq / 8 +
      (4 * Xp - 11) * (Ds + Dv) * yl / 15 -
      (4 * Xp - 11) * (Ds + Dv) * z / 5 +
      (-5 * (v - (q2 - h)) / 3 - (4 * Xp - 11) * (u + h) / 3 +
        (4 * Xp - 11) * (33 * G - 20) * (Ds + Dv) / 8) * Q) +
      5 * G * u * yl / 24 := by
  have h4 : (4 : F) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h6 : (6 : F) ≠ 0 := by convert mul_ne_zero h2 h3 using 1; ring
  have h8 : (8 : F) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  have h9 : (9 : F) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h12 : (12 : F) ≠ 0 := by convert mul_ne_zero h4 h3 using 1; ring
  have h15 : (15 : F) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; ring
  have h24 : (24 : F) ≠ 0 := by convert mul_ne_zero h8 h3 using 1; ring
  have h25 : (25 : F) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  have h72 : (72 : F) ≠ 0 := by convert mul_ne_zero h8 h9 using 1; ring
  have h100 : (100 : F) ≠ 0 := by convert mul_ne_zero h4 h25 using 1; ring
  have hPv' : Pv = Dv + (v - u) / 3 + (4 * G - 11) * (Ds + Dv) / 5 := by
    linear_combination hPv
  have hs : sN * Q = Q - 2 * dDs / 5 := by
    linear_combination (norm := (field_simp [h2, h5]; ring)) (2 / 5 : F) * hDs
  rw [original_Xi_reduction G Xn u v P Ds Dv dU dV dP dDs dDv yl ylq
      (4 * Xp - 11) h2 h3 h5 hP hDP, hPv']
  have he : Xn * (2 * dV + ylq) =
      3 * (4 * Xp - 11) * (Q - 2 * dDs / 5) := by
    calc
      _ = 3 * (4 * Xp - 11) * (sN * Q) := by rw [hXnV]; ring
      _ = _ := by rw [hs]
  calc
    _ = (P - u / 3) * y * DK - 5 * KB * yl / 6 +
      5 * G * v * dV / 12 + 5 * G * u * yl / 24 -
      G * (4 * Xp - 11) * (v * (dDs + dDv) + (Ds + Dv) * dV) / 4 -
      5 * (v - (q2 - h)) * Q / 3 -
      2 * ((4 * G - 11) + 5) * (Ds + Dv) * dV / 15 -
      (v / 9 + Dv / 3 + (4 * G - 11) * (Ds + Dv) / 15) * ylq -
      (4 * Xp - 11) * (Ds + Dv) * z / 5 -
      2 * (4 * Xp - 11) * (Ds + Dv) * dU / 15 -
      (5 * G * v / 24 + (u + h) / 9) *
        (3 * (4 * Xp - 11) * (Q - 2 * dDs / 5)) := by
      linear_combination (norm := (field_simp [h2, h3, h4, h5, h6, h9, h12, h15, h24]; ring))
        -(5 * G * v / 24 + (u + h) / 9) * he
    _ = _ := by
      rw [hU, hV]
      linear_combination (norm := (field_simp [h2, h3, h4, h5, h6, h8, h9, h12,
        h15, h24, h25, h72, h100]; ring))
        -(4 * Xp - 11) * (Ds + Dv) * (3 * dDv / 5 + 3 * Q / 2) * hGX

end WPFieldAssembly.NativeClosureLowH
