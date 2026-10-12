import WPFieldAssembly.FirstGreen
import WPFieldAssembly.NativeQuadraticInverse
import WPFieldAssembly.NativeEulerPrimitive
import WPActualNativeJacobiJet
import WPFiniteZSource

open scoped Polynomial LaurentPolynomial
open Polynomial WPActualNativeHasse WPActualNativeDegree WPActualNativeQuadraticSquare
  WPActualPositivePair WPFieldAssembly.NativeEulerPrimitive WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualRankTwoComparison WPActualGaussProper
  WPActualNativeJacobiJet WPFiniteJHighCoefficient WPFiniteCubicLog WPFiniteWSource
  WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ConicKernel WPFieldAssembly.ConicDivision

namespace WPFieldAssembly.ActualFirstGreen

set_option maxHeartbeats 1600000

variable (p : ℕ) [Fact p.Prime]

noncomputable def B : (ZMod p)[X] := actualLegendreJacobi p * properLegendreJacobi p
noncomputable def U : (ZMod p)[X] := 2 * (nativeHField p).comp (1 - X ^ 2) +
  4 * X * B p + 4 * C (WPActualGaussBottom.fieldHarmonic p (p / 6))
noncomputable def S : (ZMod p)[X] := quadraticInverse (U p)
noncomputable def J : (ZMod p)[X] := (S p).divX.comp (1 - X ^ 2)
noncomputable def M : (ZMod p)[X] := eulerPrimitive p (X * J p)
noncomputable def CBt : (ZMod p)[X] := C (1 / 5 : ZMod p) * X ^ p * (B p).comp Tc
noncomputable def CMt : (ZMod p)[X] := C (1 / 10 : ZMod p) * X ^ p * (M p).comp Tc
noncomputable def CB : (ZMod p)[X] := (contract 2 (CBt p)).comp squaredCoordinate
noncomputable def CM : (ZMod p)[X] := (contract 2 (CMt p)).comp squaredCoordinate
noncomputable def Hbar : (ZMod p)[X] := (nativeHField p).comp (WPHasseIntegralTransport.fieldV p) +
  2 * C (WPActualGaussBottom.fieldHarmonic p (p / 6))

private theorem even_expand (hp : 19 ≤ p) (P : (ZMod p)[X])
    (hev : P.comp (-X) = P) : (contract 2 P).comp (X ^ 2) = P := by
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by norm_num : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    have ho : Odd n := (Nat.even_or_odd n).resolve_left (by rintro ⟨a, ha⟩; exact hn ⟨a, by omega⟩)
    have he := congrArg (fun Q : (ZMod p)[X] => Q.coeff n) hev
    rw [coeff_comp_neg, ho.neg_pow, one_pow] at he
    have hz : (2 : ZMod p) * P.coeff n = 0 := by linear_combination -he
    exact ((mul_eq_zero.mp hz).resolve_left (small_cast_ne_zero p 2 (by omega) (by omega))).symm

theorem actual_B_odd (hp : 19 ≤ p) : (B p).comp (-X) = -B p := by
  let Y := actualLegendreJacobi p
  let n := properLegendreJacobi p
  let q : (ZMod p)[X] := 1 - X ^ 2
  let F := Y ^ 2
  let E := (B p).comp (-X) + B p
  have hY : Y ≠ 0 := by
    intro hz
    have he := actualLegendreJacobi_endpoint_one p
    change Y.eval 1 = 1 at he
    rw [hz, eval_zero] at he
    exact zero_ne_one he
  have hq : q ≠ 0 := by
    intro hz
    have he := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
    simp [q] at he
  have hw : q * (Y * n.derivative - Y.derivative * n) = 1 - Y ^ 2 :=
    properLegendreJacobi_wronskian p (by omega)
  have hFe : F.comp (-X) = F := by
    dsimp [F, Y]
    rw [← actual_native_Jacobi_square p hp, comp_assoc]
    simp [sub_comp, pow_comp]
  have hFd : F.derivative.comp (-X) = -F.derivative := by
    have he := congrArg Polynomial.derivative hFe
    simp only [derivative_comp, derivative_neg, derivative_X] at he
    linear_combination -he
  have hb : q * (F * (B p).derivative - F.derivative * B p) = F - F ^ 2 := by
    dsimp [F, B, Y, n, q]
    simp only [derivative_mul, derivative_sq, C_ofNat]
    linear_combination actualLegendreJacobi p ^ 2 * properLegendreJacobi_wronskian p (by omega)
  have hr := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hb
  simp only [mul_comp, sub_comp, pow_comp, hFe, hFd] at hr
  have hqe : q.comp (-X) = q := by simp [q, sub_comp, pow_comp]
  rw [hqe] at hr
  have hs : q * (F * E.derivative - F.derivative * E) = 0 := by
    dsimp [E]
    simp only [derivative_add, derivative_comp, derivative_neg, derivative_X]
    linear_combination hb - hr
  have hflat : E.derivative * Y - 2 * E * Y.derivative = 0 := by
    have hz : (q * Y) * (E.derivative * Y - 2 * E * Y.derivative) = 0 := by
      dsimp [F] at hs
      simp only [derivative_sq, C_ofNat] at hs
      linear_combination hs
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hq hY)
  have hBd : (B p).natDegree ≤ 2 * (p / 6) - 1 := by
    have hn := properLegendreJacobi_degree p (by omega)
    have hd := natDegree_mul_le_of_le (actualLegendreJacobi_degree p)
      (show n.natDegree ≤ p / 6 - 1 by dsimp [n]; omega)
    change (B p).natDegree ≤ p / 6 + (p / 6 - 1) at hd
    omega
  have hBE : ((B p).comp (-X)).natDegree ≤ 2 * (p / 6) - 1 :=
    natDegree_comp_le.trans
      ((Nat.mul_le_mul hBd (show (-X : (ZMod p)[X]).natDegree ≤ 1 by simp)).trans (by omega))
  have hEd : E.natDegree ≤ 2 * (p / 6) - 1 :=
    by simpa only [max_self] using natDegree_add_le_of_le hBE hBd
  have hE : E = 0 := by
    by_contra hE
    obtain ⟨k, hk, _⟩ := proper_square_division (1 / 2 : ZMod p)
      (field_half_identity p (by omega)) q Y n E hY hw hflat
    have hk0 : k ≠ 0 := by intro hz; rw [hz, mul_zero] at hk; exact hE hk
    rw [hk, natDegree_mul (pow_ne_zero 2 hY) hk0, natDegree_pow] at hEd
    dsimp [Y] at hEd
    rw [actualLegendreJacobi_exact_degree p hp] at hEd
    omega
  exact eq_neg_of_add_eq_zero_left hE

theorem actual_low_primitive (hp : 19 ≤ p) :
    (1 - X ^ 2) * J p = U p ∧ (J p).natDegree ≤ 2 * (p / 6) - 2 ∧
    (J p).natDegree < p - 1 ∧ (J p).comp (-X) = J p ∧ (M p).derivative = J p ∧
    (M p).coeff 0 = 0 ∧ (M p).comp (-X) = -M p ∧ (M p).natDegree ≤ 2 * (p / 6) - 1 := by
  let d := p / 6
  have hB := actual_B_odd p hp
  have hev : (U p).comp (-X) = U p := by
    simp only [U, add_comp, mul_comp, ofNat_comp, C_comp, comp_assoc,
      sub_comp, one_comp, pow_comp, X_comp, neg_sq, hB]
    ring
  have hH0 : (nativeHField p).eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero, nativeHField_origin]
  have hU1 : (U p).eval 1 = 0 := by
    simp [U, B, eval_comp, hH0, actualLegendreJacobi_endpoint_one, properLegendreJacobi_endpoint_one]
  have hBd : (B p).natDegree ≤ 2 * d - 1 := by
    have hd := natDegree_mul_le_of_le (actualLegendreJacobi_degree p)
      (show (properLegendreJacobi p).natDegree ≤ d - 1 by
        have := properLegendreJacobi_degree p (by omega); dsimp [d]; omega)
    change (B p).natDegree ≤ d + (d - 1) at hd
    omega
  have hqd : (1 - X ^ 2 : (ZMod p)[X]).natDegree ≤ 2 := by compute_degree
  have hHd : ((nativeHField p).comp (1 - X ^ 2)).natDegree ≤ 2 * d :=
    natDegree_comp_le.trans ((Nat.mul_le_mul (nativeHField_degree p) hqd).trans (by dsimp [d]; omega))
  have hUd : (U p).natDegree ≤ 2 * d := by
    have hform : U p = C (2 : ZMod p) * (nativeHField p).comp (1 - X ^ 2) +
        C (4 : ZMod p) * (X * B p) +
        C (4 * WPActualGaussBottom.fieldHarmonic p (p / 6)) := by
      unfold U
      rw [map_mul]
      simp only [C_ofNat]
      ring
    have hHT : (C (2 : ZMod p) * (nativeHField p).comp (1 - X ^ 2)).natDegree ≤ 2 * d :=
      (natDegree_C_mul_le _ _).trans hHd
    have hXB : (X * B p).natDegree ≤ 2 * d :=
      (natDegree_mul_le_of_le natDegree_X_le hBd).trans (by omega)
    have hBT : (C (4 : ZMod p) * (X * B p)).natDegree ≤ 2 * d :=
      (natDegree_C_mul_le _ _).trans hXB
    have hCT : (C (4 * WPActualGaussBottom.fieldHarmonic p (p / 6))).natDegree ≤ 2 * d :=
      by simp only [natDegree_C]; omega
    rw [hform]
    have hsum : (C (2 : ZMod p) * (nativeHField p).comp (1 - X ^ 2) +
        C (4 : ZMod p) * (X * B p)).natDegree ≤ 2 * d := by
      simpa only [max_self] using natDegree_add_le_of_le hHT hBT
    simpa only [max_self] using natDegree_add_le_of_le hsum hCT
  have hc := even_expand p hp (U p) hev
  have hcd : (contract 2 (U p)).natDegree ≤ d := by
    have hm : (contract 2 (U p)).natDegree * 2 ≤ 2 * d := by
      rw [← natDegree_expand 2 _, expand_eq_comp_X_pow, hc]
      exact hUd
    omega
  have hSd : (S p).natDegree ≤ d := natDegree_comp_le.trans
    ((Nat.mul_le_mul hcd (show (1 - X : (ZMod p)[X]).natDegree ≤ 1 by compute_degree)).trans (by omega))
  have hSc : (S p).comp (1 - X ^ 2) = U p := by
    rw [S, quadraticInverse, comp_assoc]
    simpa only [sub_comp, one_comp, X_comp, sub_sub_cancel] using hc
  have hS0 : (S p).coeff 0 = 0 := by
    have he := congrArg (fun P : (ZMod p)[X] => P.eval 1) hSc
    simpa [eval_comp, hU1, coeff_zero_eq_eval_zero] using he
  have hdiv : X * (S p).divX = S p := by simpa only [hS0, map_zero, add_zero] using X_mul_divX_add (S p)
  have hJ : (1 - X ^ 2) * J p = U p := by
    have he := congrArg (fun P : (ZMod p)[X] => P.comp (1 - X ^ 2)) hdiv
    simpa only [mul_comp, X_comp, J, hSc] using he
  have hJd : (J p).natDegree ≤ 2 * d - 2 := natDegree_comp_le.trans
    ((Nat.mul_le_mul (show (S p).divX.natDegree ≤ d - 1 by
      rw [natDegree_divX_eq_natDegree_tsub_one]; omega) hqd).trans (by omega))
  have hJe : (J p).comp (-X) = J p := by simp [J, comp_assoc, sub_comp, pow_comp]
  have hXd : (X * J p).natDegree ≤ 2 * d - 1 := (natDegree_mul_le_of_le natDegree_X_le hJd).trans (by omega)
  have hsmall : (X * J p).natDegree < p := by have := Nat.div_mul_le_self p 6; dsimp [d] at *; omega
  have hMD : (M p).derivative = J p :=
    mul_left_cancel₀ X_ne_zero (eulerPrimitive_derivative p (X * J p) hsmall (by simp))
  have hM0 : (M p).coeff 0 = 0 := by simp [M, eulerPrimitive_coeff]
  have hMe : (M p).comp (-X) = -M p := by
    have he : (X * J p).comp (-X) = -(X * J p) := by rw [mul_comp, X_comp, hJe]; ring
    ext n
    have hn := congrArg (fun P : (ZMod p)[X] => P.coeff n) he
    rw [coeff_comp_neg, coeff_neg] at hn
    simp only [M, coeff_comp_neg, coeff_neg, eulerPrimitive_coeff]
    linear_combination (n : ZMod p)⁻¹ * hn
  have hMd : (M p).natDegree ≤ 2 * d - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [M, eulerPrimitive_coeff, coeff_eq_zero_of_natDegree_lt (hXd.trans_lt hn), zero_div]
  have := Nat.div_mul_le_self p 6
  exact ⟨hJ, hJd, by dsimp [d] at *; omega, hJe, hMD, hM0, hMe, hMd⟩

private theorem carrier_even (hp : 19 ≤ p) (c : ZMod p) (P : (ZMod p)[X])
    (hP : P.comp (-X) = -P) :
    (C c * X ^ p * P.comp Tc).comp (-X) = C c * X ^ p * P.comp Tc := by
  have ht : (Tc : (ZMod p)[X]).comp (-X) = (-X).comp Tc := by
    simp [Tc, mul_comp, sub_comp, pow_comp]; ring
  simp only [mul_comp, C_comp, pow_comp, X_comp]
  rw [comp_assoc, ht, ← comp_assoc, hP, neg_comp,
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)).neg_pow]
  ring

theorem actual_carrier_pullbacks (hp : 19 ≤ p) :
    (CB p).comp conic = CBt p ∧ (CM p).comp conic = CMt p := by
  rcases actual_low_primitive p hp with ⟨_, _, _, _, _, _, hM, _⟩
  constructor
  · rw [CB, comp_assoc, squaredCoordinate_conic p hp]
    exact even_expand p hp (CBt p) (carrier_even p hp _ _ (actual_B_odd p hp))
  · rw [CM, comp_assoc, squaredCoordinate_conic p hp]
    exact even_expand p hp (CMt p) (carrier_even p hp _ _ hM)

theorem actual_polynomial_source (hp : 19 ≤ p) :
    2 * (WPFiniteZSource.Abar : (ZMod p)[X]) * (CM p).derivative =
      3 * squaredCoordinate ^ ((p - 1) / 2) * Hbar p + 6 * (4 * X - 11) * CB p := by
  rcases actual_low_primitive p hp with ⟨hJ, _, _, _, hMD, _, _, _⟩
  obtain ⟨hCB, hCM⟩ := actual_carrier_pullbacks p hp
  let b : (ZMod p)[X] := 4 * X ^ 2 - 1
  let c : (ZMod p)[X] := 4 * X ^ 2 - 3
  let q : (ZMod p)[X] := 1 - X ^ 2
  have unit (a : ℕ) (ha : (a : ZMod p) ≠ 0) :
      (a : (ZMod p)[X]) * C (1 / (a : ZMod p)) = 1 := by
    change C (a : ZMod p) * C (1 / (a : ZMod p)) = C 1
    rw [← C_mul, mul_one_div_cancel ha]
  have hu5 := unit 5 (small_cast_ne_zero p 5 (by omega) (by omega))
  have hu10 := unit 10 (small_cast_ne_zero p 10 (by omega) (by omega))
  have hcd : (conic : (ZMod p)[X]).derivative = 10 * X := by simp [conic, derivative_pow_succ]; ring
  have htd : (Tc : (ZMod p)[X]).derivative = 3 * b := by simp [Tc, b, derivative_pow_succ, C_ofNat]; ring
  have hn : (1 - Tc ^ 2 : (ZMod p)[X]) = q * b ^ 2 := by dsimp [q, b, Tc]; ring
  have ht : (Tc : (ZMod p)[X]) = X * c := by dsimp [Tc, c]; ring
  have hA : (WPFiniteZSource.Abar : (ZMod p)[X]).comp conic = 25 * q * b := by
    simp [WPFiniteZSource.Abar, conic, q, b, mul_comp, sub_comp]; ring
  have hl : (4 * X - 11 : (ZMod p)[X]).comp conic = 5 * c := by simp [conic, c, mul_comp, sub_comp]; ring
  have hs : (squaredCoordinate ^ ((p - 1) / 2) : (ZMod p)[X]).comp conic = X ^ (p - 1) := by
    rw [pow_comp, squaredCoordinate_conic p hp, ← pow_mul]
    congr 1
    have := half_exponent p hp
    omega
  have hjc : (1 - Tc ^ 2) * (J p).comp Tc =
      2 * (Hbar p).comp conic + 4 * Tc * (B p).comp Tc := by
    have he := congrArg (fun P : (ZMod p)[X] => P.comp Tc) hJ
    simp only [U, mul_comp, add_comp, sub_comp, pow_comp, one_comp,
      ofNat_comp, C_comp, X_comp, comp_assoc] at he
    simp only [Hbar, add_comp, mul_comp, ofNat_comp, C_comp, comp_assoc, actual_native_V_conic p hp]
    linear_combination he
  have hxpD : (X ^ p : (ZMod p)[X]).derivative = 0 := by simp [derivative_X_pow]
  have hd := congrArg Polynomial.derivative hCM
  simp only [CMt, derivative_comp, derivative_mul, derivative_C,
    hxpD, hMD, hcd, htd, zero_mul, mul_zero, zero_add, add_zero] at hd
  have hd100 : 100 * X * (CM p).derivative.comp conic = 3 * X ^ p * (J p).comp Tc * b := by
    linear_combination 10 * hd + 3 * X ^ p * (J p).comp Tc * b * hu10
  have hb5 : 5 * CBt p = X ^ p * (B p).comp Tc := by
    unfold CBt
    linear_combination X ^ p * (B p).comp Tc * hu5
  have hxp : (X : (ZMod p)[X]) ^ (p - 1) * X = X ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  let E : (ZMod p)[X] := 2 * WPFiniteZSource.Abar * (CM p).derivative -
    3 * squaredCoordinate ^ ((p - 1) / 2) * Hbar p - 6 * (4 * X - 11) * CB p
  have he : E.comp conic * (20 * X * b) = 0 := by
    simp only [E, sub_comp, mul_comp, ofNat_comp, hA, hs, hl, hCB]
    calc
      _ = 10 * q * b ^ 2 * (100 * X * (CM p).derivative.comp conic) -
        60 * (X ^ (p - 1) * X) * b * (Hbar p).comp conic -
        120 * X * b * c * (5 * CBt p) := by ring
      _ = 30 * X ^ p * b * ((1 - Tc ^ 2) * (J p).comp Tc -
          2 * (Hbar p).comp conic - 4 * Tc * (B p).comp Tc) := by rw [hd100, hxp, hb5, hn, ht]; ring
      _ = 0 := by rw [hjc]; ring
  have hb0 : b ≠ 0 := by
    intro hz
    have hh := congrArg (fun P : (ZMod p)[X] => P.coeff 0) hz
    simp [b] at hh
  have h20 : (20 : ZMod p) ≠ 0 := by
    rw [show (20 : ZMod p) = 4 * 5 by norm_num]
    exact mul_ne_zero (small_cast_ne_zero p 4 (by omega) (by omega))
      (small_cast_ne_zero p 5 (by omega) (by omega))
  have hf : (20 * X * b : (ZMod p)[X]) ≠ 0 := mul_ne_zero (mul_ne_zero (C_ne_zero.mpr h20) X_ne_zero) hb0
  have hec : E.comp conic = 0 := (mul_eq_zero.mp he).resolve_right hf
  have hdeg : (conic : (ZMod p)[X]).natDegree = 2 := by
    unfold conic
    change (C (5 : ZMod p) * X ^ 2 - 1).natDegree = 2
    compute_degree
    exact small_cast_ne_zero p 5 (by omega) (by omega)
  have he0 : E = 0 := comp_injective_nonconstant conic (by rw [hdeg]; norm_num)
    (by simpa only [zero_comp] using hec)
  dsimp [E] at he0
  linear_combination he0

noncomputable def zeta : (ZMod p)[T;T⁻¹] :=
  LaurentPolynomial.C (1 / 3 : ZMod p) * LaurentPolynomial.T (-(p : ℤ)) *
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent ^ p

theorem zeta_phase (hp : 19 ≤ p) :
    zeta p = LaurentPolynomial.C (1 / 3 : ZMod p) * WPFiniteZSource.phase p := by
  have ht : (LaurentPolynomial.T (-(p : ℤ)) * LaurentPolynomial.T (p : ℤ) :
      (ZMod p)[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  unfold zeta
  rw [WPFiniteZSource.phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1 / 3 : ZMod p) * WPFiniteZSource.phase p * ht

theorem zeta_derivative (hp : 19 ≤ p) :
    WPFiniteLaurentDifferential.D (zeta p) = 0 := by
  rw [zeta_phase p hp, WPFiniteLaurentDifferential.D_C_mul,
    WPFiniteZSource.phase_derivative, mul_zero]

theorem zeta_scale (hp : 19 ≤ p) :
    3 * zeta p * (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent ^
      ((p - 1) / 2) =
      2 * (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * WPFiniteZSource.R p := by
  have h2 := small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 := small_cast_ne_zero p 3 (by omega) (by omega)
  have unit (a : ℕ) (ha : (a : ZMod p) ≠ 0) :
      (a : (ZMod p)[T;T⁻¹]) * LaurentPolynomial.C (1 / (a : ZMod p)) = 1 := by
    change LaurentPolynomial.C (a : ZMod p) * LaurentPolynomial.C (1 / (a : ZMod p)) =
      LaurentPolynomial.C 1
    rw [← map_mul, mul_one_div_cancel ha]
  have hu2 := unit 2 h2
  have hu3 := unit 3 h3
  have hr := WPFiniteZSource.R_cleared (K := ZMod p) p hp
  rw [zeta_phase p hp]
  linear_combination -2 * hr +
    WPFiniteZSource.phase p *
      (WPFiniteWSource.squaredCoordinate : (ZMod p)[X]).toLaurent ^ ((p - 1) / 2) *
      (hu3 - hu2)

theorem actual_laurent_source (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * zeta p *
        WPFiniteLaurentDifferential.D (CM p).toLaurent =
      (WPFiniteZSource.Abar : (ZMod p)[X]).toLaurent * WPFiniteZSource.R p *
        (Hbar p).toLaurent - zeta p * (CB p).toLaurent *
          (33 - 12 * LaurentPolynomial.T 1) := by
  have he := congrArg (fun P : (ZMod p)[X] => P.toLaurent)
    (actual_polynomial_source p hp)
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat,
    Polynomial.toLaurent_X] at he
  rw [← WPFiniteLaurentDifferential.D_toLaurent] at he
  have hs := zeta_scale p hp
  have h2L : (2 : (ZMod p)[T;T⁻¹]) ≠ 0 := by
    change LaurentPolynomial.C (2 : ZMod p) ≠ 0
    intro hz
    have hc := congrArg (fun F : (ZMod p)[T;T⁻¹] => F.coeff 0) hz
    have hc' : (2 : ZMod p) = 0 := by simpa using hc
    exact (small_cast_ne_zero p 2 (by omega) (by omega)) hc'
  apply mul_left_cancel₀ h2L
  linear_combination zeta p * he + (Hbar p).toLaurent * hs

end WPFieldAssembly.ActualFirstGreen
