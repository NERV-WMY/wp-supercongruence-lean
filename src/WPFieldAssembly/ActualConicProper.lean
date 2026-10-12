import WPActualNativeJacobiJet

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualNativeQuadraticSquare
  WPActualRankTwoLegendreField WPActualRankTwoProper
  WPActualNativeJacobiJet WPFiniteLVSource
  WPFiniteJHighCoefficient WPFiniteCubicLog WPHasseIntegralTransport

namespace WPFieldAssembly.ActualConicProper

noncomputable def conicA {K : Type*} [CommRing K] : K[X] :=
  (1 - X ^ 2) * (4 * X ^ 2 - 1)

theorem actual_degree_from_class (p d : ℕ)
    (hc : p = 6 * d + 1 ∨ p = 6 * d + 5) : p / 6 = d := by
  rcases hc with hc | hc <;> omega

theorem cubic_factor {K : Type*} [Field K] :
    (Tc : K[X]) = X * (4 * X ^ 2 - 3) := by
  unfold Tc
  ring

theorem cubic_chain_scale {K : Type*} [Field K]
    (a : K) (ha : 3 * a = 1) :
    conicA * C a * (Tc : K[X]).derivative = 1 - Tc ^ 2 := by
  have hC : (3 : K[X]) * C a = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (C : K → K[X]) ha
  have hD : (Tc : K[X]).derivative = 3 * (4 * X ^ 2 - 1) := by
    simp [Tc, derivative_pow_succ, map_ofNat]
    ring
  have hfactor : (1 - Tc ^ 2 : K[X]) = conicA * (4 * X ^ 2 - 1) := by
    unfold Tc conicA
    ring
  calc
    conicA * C a * (Tc : K[X]).derivative =
        conicA * (3 * C a) * (4 * X ^ 2 - 1) := by rw [hD]; ring
    _ = conicA * (4 * X ^ 2 - 1) := by rw [hC, mul_one]
    _ = 1 - Tc ^ 2 := hfactor.symm

theorem cubic_proper_wronskian {K : Type*} [Field K]
    (a : K) (ha : 3 * a = 1) (Y N : K[X])
    (hW : (1 - X ^ 2) * (Y * N.derivative - Y.derivative * N) = 1 - Y ^ 2) :
    conicA * (Y.comp Tc * (C a * N.comp Tc).derivative -
      (Y.comp Tc).derivative * (C a * N.comp Tc)) = 1 - (Y.comp Tc) ^ 2 := by
  have hcomp := congrArg (fun P : K[X] => P.comp Tc) hW
  simp only [mul_comp, sub_comp, pow_comp, one_comp, X_comp] at hcomp
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp]
  calc
    _ = (conicA * C a * (Tc : K[X]).derivative) *
        (Y.comp Tc * N.derivative.comp Tc - Y.derivative.comp Tc * N.comp Tc) := by ring
    _ = (1 - Tc ^ 2) *
        (Y.comp Tc * N.derivative.comp Tc - Y.derivative.comp Tc * N.comp Tc) := by
      rw [cubic_chain_scale a ha]
    _ = 1 - (Y.comp Tc) ^ 2 := hcomp

theorem actual_conic_proper_wronskian (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let y := (actualLegendreJacobi p).comp Tc
    let m := C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc
    ((1 - X ^ 2) * (4 * X ^ 2 - 1)) *
      (y * m.derivative - y.derivative * m) = 1 - y ^ 2 := by
  dsimp only
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have ha : (3 : ZMod p) * (1 / 3) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ h3
  exact cubic_proper_wronskian (1 / 3 : ZMod p) ha
    (actualLegendreJacobi p) (properLegendreJacobi p)
    (properLegendreJacobi_wronskian p (by omega))

theorem actual_full_native_conic_square (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((nativeField p ((p - 1) / 2)).comp (fieldV p)).comp (5 * X ^ 2 - 1) =
      ((actualLegendreJacobi p).comp Tc) ^ 2 := by
  change ((nativeField p ((p - 1) / 2)).comp (fieldV p)).comp
      (conic : (ZMod p)[X]) = _
  rw [comp_assoc, actual_native_V_conic p hp]
  rw [actual_full_native_field_cutoff p ((p - 1) / 2)
    (by omega) (by omega) (by
      have := Nat.div_mul_le_self p 6
      have := WPFiniteWSource.half_exponent p hp
      omega)]
  have he := congrArg (fun P : (ZMod p)[X] => P.comp Tc)
    (actual_native_Jacobi_square p hp)
  simpa only [comp_assoc, sub_comp, one_comp, pow_comp, X_comp] using he

end WPFieldAssembly.ActualConicProper
