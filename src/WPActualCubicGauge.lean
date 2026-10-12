import WPActualCMGaussSquare

open scoped Polynomial
open Polynomial WPActualCMGaussSquare

namespace WPActualCubicGauge

noncomputable def cubicH {K : Type*} [CommRing K] : K[X] := 1 + 8 * X
noncomputable def cubicA {K : Type*} [CommRing K] : K[X] := 64 * X * (1 - X) ^ 3
noncomputable def cubicB {K : Type*} [CommRing K] : K[X] :=
  64 * (1 - X) ^ 2 * (1 - 20 * X - 8 * X ^ 2)

theorem cubicH_derivative {K : Type*} [CommRing K] :
    (cubicH : K[X]).derivative = 8 := by simp [cubicH]

theorem cubicB_source {K : Type*} [CommRing K] :
    cubicB = (cubicA : K[X]).derivative * cubicH - 24 * cubicA := by
  simp [cubicB, cubicA, cubicH, derivative_mul, derivative_pow_succ, C_ofNat]
  ring

noncomputable def nativeGaugeSource {K : Type*} [CommRing K] (A B C D : K[X]) : K[X] :=
  72 * cubicA ^ 2 * (cubicH ^ 3 - cubicA) * D +
    (216 * cubicA * cubicH ^ 6 - 324 * cubicA ^ 2 * cubicH ^ 3) * C +
    (72 * cubicH ^ 9 - 226 * cubicA * cubicH ^ 6) * B - 5 * cubicH ^ 9 * A

theorem cubicGauge_second {K : Type*} [CommRing K] (A B C : K[X])
    (hA : cubicH ^ 4 * A.derivative + 4 * cubicH ^ 3 * A = cubicB * B)
    (hB : cubicH ^ 4 * B.derivative + 4 * cubicH ^ 3 * B = cubicB * C) :
    cubicH ^ 8 * A.derivative.derivative =
      48 * cubicH ^ 6 * A +
        (cubicH ^ 4 * cubicB.derivative - 40 * cubicH ^ 3 * cubicB) * B + cubicB ^ 2 * C := by
  have hd := congrArg Polynomial.derivative hA
  simp only [derivative_add, derivative_mul, derivative_pow_succ,
    derivative_ofNat, cubicH_derivative, Nat.cast_ofNat, zero_mul, zero_add] at hd
  norm_num only at hd
  simp only [C_ofNat] at hd
  linear_combination cubicH ^ 4 * hd + cubicB * hB - 36 * cubicH ^ 3 * hA

theorem cubicGauge_third {K : Type*} [CommRing K] (A B C D : K[X])
    (hA : cubicH ^ 4 * A.derivative + 4 * cubicH ^ 3 * A = cubicB * B)
    (hB : cubicH ^ 4 * B.derivative + 4 * cubicH ^ 3 * B = cubicB * C)
    (hC : cubicH ^ 4 * C.derivative + 4 * cubicH ^ 3 * C = cubicB * D) :
    cubicH ^ 12 * A.derivative.derivative.derivative =
      -960 * cubicH ^ 9 * A +
        (cubicH ^ 8 * cubicB.derivative.derivative -
          76 * cubicH ^ 7 * cubicB.derivative + 1808 * cubicH ^ 6 * cubicB) * B +
        (3 * cubicH ^ 4 * cubicB * cubicB.derivative - 108 * cubicH ^ 3 * cubicB ^ 2) * C +
        cubicB ^ 3 * D := by
  have hs := cubicGauge_second A B C hA hB
  have hd := congrArg Polynomial.derivative hs
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_pow_succ,
    derivative_ofNat, cubicH_derivative, Nat.cast_ofNat, zero_mul, zero_add] at hd
  norm_num only at hd
  simp only [C_ofNat] at hd
  linear_combination cubicH ^ 4 * hd + 48 * cubicH ^ 6 * hA +
    (cubicH ^ 4 * cubicB.derivative - 40 * cubicH ^ 3 * cubicB) * hB +
    cubicB ^ 2 * hC - 64 * cubicH ^ 3 * hs

/-- Complete cubic gauge transport of the native third-order source. -/
theorem cubicGauge_source {K : Type*} [CommRing K] (A B C D : K[X])
    (hA : cubicH ^ 4 * A.derivative + 4 * cubicH ^ 3 * A = cubicB * B)
    (hB : cubicH ^ 4 * B.derivative + 4 * cubicH ^ 3 * B = cubicB * C)
    (hC : cubicH ^ 4 * C.derivative + 4 * cubicH ^ 3 * C = cubicB * D) :
    8 * cubicH ^ 12 * squareRegular A = cubicB * nativeGaugeSource A B C D := by
  have hs := cubicGauge_second A B C hA hB
  have ht := cubicGauge_third A B C D hA hB hC
  simp [cubicH, cubicB, derivative_mul, derivative_pow_succ] at hs ht hA
  unfold squareRegular nativeGaugeSource cubicH cubicA cubicB
  linear_combination 72 * X ^ 2 * (1 - X) ^ 2 * ht +
    216 * X * (1 - X) * (1 - 2 * X) * (1 + 8 * X) ^ 4 * hs +
    8 * (9 - 62 * X + 62 * X ^ 2) * (1 + 8 * X) ^ 8 * hA

end WPActualCubicGauge
