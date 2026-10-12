import WPFieldAssembly.NativePrecision
import WPActualNativeDegree

open scoped Polynomial
open Polynomial WPPIntegralReduction WPActualNativeHasse WPActualNativeParameter
  WPActualNativeFirstJet WPActualNativeJetODE WPActualNativeFirstIntegral
  WPActualNativeDegree WPFieldAssembly.NativePrecision

namespace WPFieldAssembly.NativeTerminal

set_option maxHeartbeats 800000

/-- The original prime-class sign, distinct from the logarithmic eta differential. -/
def nativeSixEta (p : ℕ) : ℤ := if p % 6 = 1 then 1 else -1

theorem first_integral_terminal {K : Type*} [Field K] (F J : K[X]) (d N : ℕ)
    (hF : F.natDegree ≤ d) (hJ : J.natDegree ≤ N) (hdN : d < N)
    (hFd : F.coeff d ≠ 0)
    (hsource : X * (F * J.derivative - F.derivative * J) = F * ((1 - X) ^ N - F)) :
    ((N : K) - (d : K)) * J.coeff N = (-1 : K) ^ N := by
  have htheta (P : K[X]) : (theta P).natDegree ≤ P.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [theta_coeff, coeff_eq_zero_of_natDegree_lt hn, mul_zero]
  have hlin : (1 - X : K[X]).natDegree ≤ 1 := by
    simpa using natDegree_sub_le_of_le (show (1 : K[X]).natDegree ≤ 0 by simp)
      (natDegree_X_le (R := K))
  have hH : ((1 - X : K[X]) ^ N).natDegree ≤ N := by
    simpa only [Nat.mul_one] using power_degree_bound (1 - X : K[X]) 1 N hlin
  have hsq : (F ^ 2).natDegree ≤ d + d := by
    simpa only [pow_two] using natDegree_mul_le_of_le hF hF
  have hsqc : (F ^ 2).coeff (d + N) = 0 :=
    coeff_eq_zero_of_natDegree_lt (hsq.trans_lt (by omega))
  have hHc : ((1 - X : K[X]) ^ N).coeff N = (-1 : K) ^ N := by
    have he : (1 - X : K[X]) ^ N = ((1 + X) ^ N).comp (C (-1) * X) := by
      simp only [pow_comp, add_comp, one_comp, X_comp, C_neg, C_1, neg_mul, one_mul]
      rfl
    rw [he, comp_C_mul_X_coeff, coeff_one_add_X_pow]
    simp
  have hleft₁ : (F * theta J).coeff (d + N) = F.coeff d * (N : K) * J.coeff N := by
    rw [coeff_mul_add_eq_of_natDegree_le hF ((htheta J).trans hJ), theta_coeff]
    ring
  have hleft₂ : (theta F * J).coeff (d + N) = (d : K) * F.coeff d * J.coeff N := by
    rw [coeff_mul_add_eq_of_natDegree_le ((htheta F).trans hF) hJ, theta_coeff]
  have hright : (F * (1 - X) ^ N).coeff (d + N) = F.coeff d * (-1 : K) ^ N := by
    rw [coeff_mul_add_eq_of_natDegree_le hF hH, hHc]
  have he : F * theta J - theta F * J = F * (1 - X) ^ N - F ^ 2 := by
    dsimp only [theta]
    linear_combination hsource
  have hc := congrArg (fun P : K[X] => P.coeff (d + N)) he
  rw [coeff_sub, coeff_sub, hleft₁, hleft₂, hright, hsqc, sub_zero] at hc
  have hz : F.coeff d * (((N : K) - (d : K)) * J.coeff N - (-1 : K) ^ N) = 0 := by
    linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hFd)

theorem actual_native_half_jet_terminal (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ((((p - 1) / 2 : ℕ) : ZMod p) - ((p / 6 : ℕ) : ZMod p)) *
      (parameterJet ((p - 1) / 2) (-(p : ℚ) / 6) : ZMod p) =
        (-1 : ZMod p) ^ ((p - 1) / 2) := by
  have hFd : (nativeField p (p / 6)).coeff (p / 6) ≠ 0 := by
    rw [nativeField_coeff, if_pos (by omega)]
    exact actual_native_coefficient_field_unit p (p / 6) (by omega) (by omega)
  have he := first_integral_terminal (nativeField p (p / 6)) (nativeJetField p)
    (p / 6) ((p - 1) / 2) (actual_native_field_degree p) (nativeJetField_degree p)
    (by omega) hFd (actual_native_first_integral p hp)
  rw [nativeJetField_coeff, if_pos (by omega)] at he
  exact he

/-- The actual integral quotient has its original terminal constant in both prime classes. -/
theorem actual_native_half_div_prime_residue (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (nativeHalfDivPrime p hp) =
      -(nativeSixEta p : ZMod p) * (-1 : ZMod p) ^ ((p - 1) / 2) / 2 := by
  let d := p / 6
  let N := (p - 1) / 2
  let j : ZMod p := (parameterJet N (-(p : ℚ) / 6) : ZMod p)
  let s : ZMod p := (-1 : ZMod p) ^ N
  have htop := actual_native_half_jet_terminal p hp
  change ((N : ZMod p) - (d : ZMod p)) * j = s at htop
  have hhalf := WPFiniteWSource.half_exponent p hp
  have h2 : (2 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  change ((WPReview.nativeCoefficient N / (p : ℚ) : ℚ) : ZMod p) = _
  rw [actual_high_first_jet_coefficient p N (by omega) (by omega) (by omega)]
  change (1 / 6 : ZMod p) * j = -(nativeSixEta p : ZMod p) * s / 2
  rcases prime_six_classes p (by omega) with h1 | h5
  · have hN : N = 3 * d := by dsimp [N, d]; omega
    have hNc : (N : ZMod p) = 3 * (d : ZMod p) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ZMod p)) hN
    have hdc : 6 * (d : ZMod p) + 1 = 0 := by
      have hc := congrArg (fun n : ℕ => (n : ZMod p)) h1
      simpa only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one, ZMod.natCast_self] using hc.symm
    rw [hNc] at htop
    have hj : j = -3 * s := by linear_combination -3 * htop + j * hdc
    have heta : nativeSixEta p = 1 := by
      have hm : p % 6 = 1 := by omega
      simp [nativeSixEta, hm]
    rw [heta, hj]
    norm_num only [Int.cast_one]
    field_simp [h2, h6]
    ring
  · have hN : N = 3 * d + 2 := by dsimp [N, d]; omega
    have hNc : (N : ZMod p) = 3 * (d : ZMod p) + 2 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ZMod p)) hN
    have hdc : 6 * (d : ZMod p) + 5 = 0 := by
      have hc := congrArg (fun n : ℕ => (n : ZMod p)) h5
      simpa only [d, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        ZMod.natCast_self] using hc.symm
    rw [hNc] at htop
    have hj : j = 3 * s := by linear_combination 3 * htop - j * hdc
    have heta : nativeSixEta p = -1 := by
      have hm : p % 6 ≠ 1 := by omega
      simp [nativeSixEta, hm]
    rw [heta, hj]
    norm_num only [Int.cast_neg, Int.cast_one, neg_neg]
    field_simp [h2, h6]
    ring

end WPFieldAssembly.NativeTerminal
