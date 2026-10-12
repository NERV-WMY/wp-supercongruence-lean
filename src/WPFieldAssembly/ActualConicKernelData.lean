import WPFieldAssembly.ActualConicSource
import WPFieldAssembly.NativeConicTerminal
import WPActualNativeDegree

open scoped Polynomial
open Polynomial WPActualNativeHasse WPActualRankTwoComparison
  WPActualRankTwoLegendreField WPActualNativeDegree
  WPFieldAssembly.ConicDivision WPFieldAssembly.ActualConicProper
  WPFieldAssembly.ActualConicSource WPFieldAssembly.ConicCoefficients
  WPFieldAssembly.NativeShiftedChi WPFieldAssembly.NativeConicTerminal
  WPFieldAssembly.NativeTerminal WPFiniteCubicLog

namespace WPFieldAssembly.ActualConicKernelData

set_option maxHeartbeats 1200000

/-- Multiplication by X preserves the terminal slot in the degree argument. -/
theorem quotient_degree_top {K : Type*} [Field K]
    (A y H E b : K[X]) (n h : ℕ) (hy : y ≠ 0) (hyn : y.natDegree = n)
    (hH : H.natDegree ≤ h) (hA : A.natDegree ≤ 4) (hA4 : A.coeff 4 = -4)
    (hE : (X * E * y ^ 3).natDegree < n + h + 4)
    (hMb : firstNumerator A y H E = y * b) :
    b.natDegree ≤ h + 3 ∧
      b.coeff (h + 3) = -4 * H.coeff h * ((h : K) - 2 * (n : K)) := by
  have hny : y.natDegree ≤ n := by omega
  have hty := (theta_degree_le y).trans hny
  have htH := (theta_degree_le H).trans hH
  let I := y * theta H - 2 * theta y * H
  have hI : I.natDegree ≤ n + h := by
    have h1 := natDegree_mul_le_of_le hny htH
    have h2 := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (show (2 : K[X]).natDegree ≤ 0 by simp) hty) hH
    exact (natDegree_sub_le_of_le h1 h2).trans (by omega)
  have hXm : X * (y * b) = A * I + X * E * y ^ 3 := by
    rw [← hMb]
    dsimp only [I, firstNumerator, theta]
    ring
  have hbound : (X * (y * b)).natDegree ≤ n + h + 4 := by
    rw [hXm]
    exact (natDegree_add_le_of_le (natDegree_mul_le_of_le hA hI)
      (Nat.le_of_lt hE)).trans (by omega)
  have hbdeg : b.natDegree ≤ h + 3 := by
    by_cases hb : b = 0
    · subst b; simp
    · rw [natDegree_mul X_ne_zero (mul_ne_zero hy hb),
        natDegree_mul hy hb, natDegree_X, hyn] at hbound
      omega
  refine ⟨hbdeg, ?_⟩
  have hleft : (X * (y * b)).coeff (n + h + 4) = y.coeff n * b.coeff (h + 3) := by
    rw [show n + h + 4 = (n + (h + 3)) + 1 by omega, coeff_X_mul]
    exact coeff_mul_add_eq_of_natDegree_le hny hbdeg
  have hfirst := coeff_mul_add_eq_of_natDegree_le hny htH
  have hsecond := coeff_mul_add_eq_of_natDegree_le hty hH
  have hItop : I.coeff (n + h) = y.coeff n * H.coeff h * ((h : K) - 2 * (n : K)) := by
    have hi : I = y * theta H - 2 * (theta y * H) := by dsimp only [I]; ring
    rw [hi, coeff_sub, coeff_ofNat_mul, hfirst, hsecond, theta_coeff, theta_coeff]
    ring
  have hApart : (A * I).coeff (n + h + 4) =
      -4 * (y.coeff n * H.coeff h * ((h : K) - 2 * (n : K))) := by
    rw [show n + h + 4 = 4 + (n + h) by omega,
      coeff_mul_add_eq_of_natDegree_le hA hI, hA4, hItop]
  have hc := congrArg (fun P : K[X] => P.coeff (n + h + 4)) hXm
  rw [hleft, coeff_add, hApart, coeff_eq_zero_of_natDegree_lt hE, add_zero] at hc
  have hcy : y.coeff n ≠ 0 := by
    rw [← hyn, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hy
  apply mul_left_cancel₀ hcy
  calc
    y.coeff n * b.coeff (h + 3) =
        -4 * (y.coeff n * H.coeff h * ((h : K) - 2 * (n : K))) := hc
    _ = y.coeff n * (-4 * H.coeff h * ((h : K) - 2 * (n : K))) := by ring

theorem even_derivative {K : Type*} [CommRing K] (P : K[X]) (hP : P.comp (-X) = P) :
    P.derivative.comp (-X) = -P.derivative := by
  have hd := congrArg Polynomial.derivative hP
  simp only [derivative_comp, derivative_neg, derivative_X] at hd
  linear_combination -hd

theorem even_source_odd_quotient {K : Type*} [CommRing K] [IsDomain K]
    (A F H E b : K[X]) (hF0 : F ≠ 0) (hA : A.comp (-X) = A) (hF : F.comp (-X) = F)
    (hH : H.comp (-X) = H) (hE : E.comp (-X) = -E)
    (hform : F * b = A * (F * H.derivative - F.derivative * H) + E * F ^ 2) :
    b.comp (-X) = -b := by
  have hHD := even_derivative H hH
  have hFD := even_derivative F hF
  have hr := congrArg (fun P : K[X] => P.comp (-X)) hform
  simp only [mul_comp, add_comp, sub_comp, pow_comp, hA, hF, hH, hE, hHD, hFD] at hr
  have hz : F * (b.comp (-X) + b) = 0 := by linear_combination hr + hform
  exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left hF0)

theorem actual_kernel_data (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) (b : (ZMod p)[X])
    (hMb : firstNumerator conicA ((actualLegendreJacobi p).comp Tc)
      ((shiftedChiField p hp).comp B) (forcingE p) = (actualLegendreJacobi p).comp Tc * b)
    (hAb : (conicA : (ZMod p)[X]) ∣ b) :
    b.natDegree ≤ 5 * p ∧ b.comp (-X) = -b ∧ b.eval 1 = 0 ∧
      b.eval (1 / 2) = 0 ∧ b.coeff (5 * p) = -20 := by
  let y := (actualLegendreJacobi p).comp Tc
  let H := (shiftedChiField p hp).comp B
  let n := 3 * (p / 6)
  let h := 5 * p - 3
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hTc : (Tc : (ZMod p)[X]).natDegree = 3 := by
    apply le_antisymm
    · unfold Tc; compute_degree
    · apply le_natDegree_of_ne_zero
      simpa [Tc, coeff_X] using h4
  have hyn : y.natDegree = n := by
    dsimp only [y, n]
    rw [natDegree_comp, actualLegendreJacobi_exact_degree p hp, hTc]
    omega
  have hy : y ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hyn
    dsimp only [n] at hyn
    omega
  have hBdeg : (B : (ZMod p)[X]).natDegree ≤ 2 := by unfold B; compute_degree
  have hHdeg : H.natDegree ≤ h := by
    have hd := (natDegree_comp_le (p := shiftedChiField p hp) (q := B)).trans
      (Nat.mul_le_mul (shiftedChiField_degree p hp) hBdeg)
    change H.natDegree ≤ (p + 3 * ((p - 1) / 2)) * 2 at hd
    have hh := WPFiniteWSource.half_exponent p hp
    exact hd.trans (by dsimp only [h]; omega)
  have hHtop : H.coeff h = -5 * (nativeSixEta p : ZMod p) / 2 := by
    dsimp only [H, h]
    exact actual_conic_H_terminal p hp
  have hAdeg : (conicA : (ZMod p)[X]).natDegree ≤ 4 := by unfold conicA; compute_degree
  have hAnorm : (conicA : (ZMod p)[X]) = -(4 * X ^ 4) + 5 * X ^ 2 - 1 := by
    unfold conicA; ring
  have hA4 : (conicA : (ZMod p)[X]).coeff 4 = -4 := by
    rw [hAnorm]
    simp [coeff_one]
  have hEdeg : (forcingE p).natDegree ≤ 2 * p + 3 := by
    have hf : (5 * X * conicA : (ZMod p)[X]).natDegree ≤ 5 := by
      unfold conicA; compute_degree
    have hb := WPActualNativeFirstIntegral.power_degree_bound (B : (ZMod p)[X]) 2 (p - 1) hBdeg
    exact (natDegree_mul_le_of_le hf hb).trans (by omega)
  have hEstrict : (X * forcingE p * y ^ 3).natDegree < n + h + 4 := by
    have hd := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_X_le (R := ZMod p)) hEdeg)
      (WPActualNativeFirstIntegral.power_degree_bound y n 3 (by omega))
    have hd6 := Nat.div_mul_le_self p 6
    exact hd.trans_lt (by dsimp only [n, h]; omega)
  have hMb' : firstNumerator conicA y H (forcingE p) = y * b := hMb
  have hdata := quotient_degree_top conicA y H (forcingE p) b n h hy hyn hHdeg hAdeg hA4 hEstrict hMb'
  have hidx : h + 3 = 5 * p := by dsimp only [h]; omega
  have hbdeg : b.natDegree ≤ 5 * p := by simpa only [hidx] using hdata.1
  have hBneg : (B : (ZMod p)[X]).comp (-X) = B := by simp [B, mul_comp, sub_comp, pow_comp]
  have hAneg : (conicA : (ZMod p)[X]).comp (-X) = conicA := by simp [conicA, mul_comp, sub_comp, pow_comp]
  have hHneg : H.comp (-X) = H := by dsimp only [H]; rw [comp_assoc, hBneg]
  have hf : ((nativeField p ((p - 1) / 2)).comp (WPHasseIntegralTransport.fieldV p)).comp B = y ^ 2 := by
    dsimp only [y]
    exact actual_full_native_conic_square p hp
  have hFneg : (y ^ 2).comp (-X) = y ^ 2 := by rw [← hf, comp_assoc, hBneg]
  have hEneg : (forcingE p).comp (-X) = -forcingE p := by
    simp only [forcingE, mul_comp, pow_comp, ofNat_comp, X_comp, hAneg, hBneg]
    ring
  have hform : y ^ 2 * b = conicA *
      (y ^ 2 * H.derivative - (y ^ 2).derivative * H) + forcingE p * (y ^ 2) ^ 2 := by
    calc
      y ^ 2 * b = y * firstNumerator conicA y H (forcingE p) := by rw [hMb']; ring
      _ = _ := by simp only [firstNumerator, derivative_sq, C_ofNat]; ring
  have hbodd := even_source_odd_quotient conicA (y ^ 2) H (forcingE p) b
    (pow_ne_zero 2 hy) hAneg hFneg hHneg hEneg hform
  obtain ⟨k, hk⟩ := hAb
  have hb1 : b.eval 1 = 0 := by rw [hk]; simp [conicA]
  have hhalfA : (conicA : (ZMod p)[X]).eval (1 / 2) = 0 := by
    have hs : (4 : ZMod p) * (1 / 2) ^ 2 = 1 := by field_simp [h2]; ring
    simp only [conicA, eval_mul, eval_sub, eval_one, eval_ofNat, eval_pow, eval_X]
    rw [hs, sub_self, mul_zero]
  have hbhalf : b.eval (1 / 2) = 0 := by rw [hk, eval_mul, hhalfA, zero_mul]
  have hhcast : ((5 * p - 3 : ℕ) : ZMod p) = -3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 5 * p), Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self]
    ring
  have hfac : (h : ZMod p) - 2 * (n : ZMod p) = -2 * (nativeSixEta p : ZMod p) := by
    dsimp only [n, h]
    rw [hhcast]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rcases WPActualNativeParameter.prime_six_classes p (by omega) with hp1 | hp5
    · have hc : 6 * ((p / 6 : ℕ) : ZMod p) + 1 = 0 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          ZMod.natCast_self] using (congrArg (fun j : ℕ => (j : ZMod p)) hp1).symm
      have heta : nativeSixEta p = 1 := by
        have hm : p % 6 = 1 := by omega
        simp [nativeSixEta, hm]
      rw [heta]
      norm_num only [Int.cast_one]
      linear_combination -hc
    · have hc : 6 * ((p / 6 : ℕ) : ZMod p) + 5 = 0 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          ZMod.natCast_self] using (congrArg (fun j : ℕ => (j : ZMod p)) hp5).symm
      have heta : nativeSixEta p = -1 := by
        have hm : p % 6 ≠ 1 := by omega
        simp [nativeSixEta, hm]
      rw [heta]
      norm_num only [Int.cast_neg, Int.cast_one, neg_neg]
      linear_combination -hc
  have hetaSq : (nativeSixEta p : ZMod p) ^ 2 = 1 := by unfold nativeSixEta; split_ifs <;> norm_num
  have htop := hdata.2
  rw [hidx, hHtop, hfac] at htop
  have hbtop : b.coeff (5 * p) = -20 := by
    calc
      b.coeff (5 * p) = -4 * (-5 * (nativeSixEta p : ZMod p) / 2) *
        (-2 * (nativeSixEta p : ZMod p)) := htop
      _ = -20 * (nativeSixEta p : ZMod p) ^ 2 := by field_simp [h2]; ring
      _ = -20 := by rw [hetaSq]; ring
  exact ⟨hbdeg, hbodd, hb1, hbhalf, hbtop⟩

end WPFieldAssembly.ActualConicKernelData
