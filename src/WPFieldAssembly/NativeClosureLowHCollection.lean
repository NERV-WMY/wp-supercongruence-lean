import WPFieldAssembly.NativeClosureLowHIdentity

namespace WPFieldAssembly.NativeClosureLowH

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: This is the product-derivative collection inside the
original Euler adjoint of actualZ52=(u-v)^2+6*v*(P-Dstar). The symbols dU,
dV, dP, dDs and the logarithmic densities already include the same H(V)
multiplier. The two printed finite-source equations retain the actual
half-Frobenius phase. The result identifies the entire Z52 derivative with
the original IR64d Xi block and its remaining branch density. It neither
identifies a free carrier with actualZ52 nor evaluates a residue; those
actual attachments belong to the source consumer. -/

/-- The complete Z52 product derivative yields the original Xi block and
its exact remaining branch contribution to the low H collector. -/
theorem original_Z52_H_collection {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (G Xn sN Bp φ u v P Ds dU dV dP dDs yl ylq Q : F)
    (hU : 2 * dU + yl = -3 * Bp * sN * Q)
    (hV : Xn * (2 * dV + ylq) = 3 * φ * sN * Q) :
    -5 * G * (2 * (u - v) * (dU - dV) +
        6 * (dV * (P - Ds) + v * (dP - dDs))) / 24 =
      (5 * G * (v * dU + (u - (1 + Xn) * v) * dV) / 12 +
        5 * G * (u * yl - Xn * v * ylq) / 24 -
        5 * G * (v * (dP - dDs) + (P - Ds) * dV) / 4) +
      5 * G * sN * (Bp * u + φ * v) * Q / 8 := by
  have h4 : (4 : F) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1
    norm_num
  have h8 : (8 : F) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1
    norm_num
  have h12 : (12 : F) ≠ 0 := by
    convert mul_ne_zero h4 h3 using 1
    ring
  have h24 : (24 : F) ≠ 0 := by
    convert mul_ne_zero h8 h3 using 1
    ring
  linear_combination (norm := (field_simp [h4, h8, h12, h24]; ring))
    (-5 * G * u / 24) * hU + (5 * G * v / 24) * hV

end WPFieldAssembly.NativeClosureLowH
