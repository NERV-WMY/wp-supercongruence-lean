import WPActualNativeDegree
import WPActualPositivePair

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeDegree WPActualPositivePair

namespace WPFieldAssembly.NativeEulerPrimitive

/-- The canonical native Euler primitive, with its full degree-d coefficient range. -/
noncomputable def nativeHField (p : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  eulerPrimitive p (nativeField p (p / 6))

theorem nativeHField_coeff (p n : ℕ) [Fact p.Prime] :
    (nativeHField p).coeff n =
      (if n ≤ p / 6 then (WPReview.nativeCoefficient n : ZMod p) else 0) / (n : ZMod p) := by
  rw [nativeHField, eulerPrimitive_coeff, nativeField_coeff]
  simp only [Nat.lt_succ_iff]

theorem nativeHField_degree (p : ℕ) [Fact p.Prime] :
    (nativeHField p).natDegree ≤ p / 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [nativeHField_coeff, if_neg (by omega), zero_div]

theorem nativeHField_origin (p : ℕ) [Fact p.Prime] : (nativeHField p).coeff 0 = 0 := by
  rw [nativeHField_coeff]
  simp

end WPFieldAssembly.NativeEulerPrimitive
