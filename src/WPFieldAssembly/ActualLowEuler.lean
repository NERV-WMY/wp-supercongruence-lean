import WPFieldAssembly.NativeScalarRows
import WPFieldAssembly.ActualBalancedCarry
import WPActualNativeQuadraticSquare
import WPActualHasseReciprocal

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource
  WPFiniteLaurentDifferential
  WPFieldAssembly.NativeScalarRows
  WPFieldAssembly.ActualR0Node
  WPFieldAssembly.NativeQuadraticInverse
  WPFieldAssembly.ResidualProjection
  WPFieldAssembly.ActualDeltaUNextSource
  WPActualRankTwoLegendreField WPActualNativeHasse
  WPFiniteCarry WPPIntegralReduction

namespace WPFieldAssembly.ActualLowEuler

variable {K : Type*} [Field K]

noncomputable def lowKernel : K[T;T⁻¹] :=
  LaurentPolynomial.C ((125 : K)⁻¹) * (4 * T 1 - 1) * (12 * T (-1) - 33)

noncomputable def lowU (E : K[X]) : K[T;T⁻¹] :=
  lowKernel * substituteOver E.divX
    (WPFiniteNC122Residue.Qrev : K[X]).toLaurent

theorem T_one_inverse :
    (T 1 : K[T;T⁻¹]) * T (-1) = 1 := by
  rw [← T_add]
  norm_num

theorem Frev_laurent_kernel :
    (WPFiniteNC122Residue.Frev : K[X]).toLaurent =
      -(T 2 * (lowKernel : K[T;T⁻¹])) := by
  have hf : (WPFiniteNC122Residue.Frev : K[X]) =
      Polynomial.C ((125 : K)⁻¹) * 3 * X *
        (4 * X - 1) * (11 * X - 4) := by
    unfold WPFiniteNC122Residue.Frev
    simp only [div_eq_mul_inv, map_mul, map_ofNat]
    ring
  have ht2 : (T 2 : K[T;T⁻¹]) = T 1 ^ 2 := by
    rw [T_pow]
    norm_num
  rw [hf]
  simp only [map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  rw [ht2]
  unfold lowKernel
  linear_combination
    12 * LaurentPolynomial.C ((125 : K)⁻¹) * T 1 * (4 * T 1 - 1) *
      (T_one_inverse (K := K))

theorem D_originalQ_factor :
    D (originalQ : K[T;T⁻¹]) =
      -LaurentPolynomial.C ((125 : K)⁻¹) * 3 * T (-1) ^ 2 *
        (4 * T (-1) - 1) * (11 - 4 * T (-1)) := by
  have hd : (WPFiniteNC122Residue.Qrev : K[X]).derivative =
      Polynomial.C ((125 : K)⁻¹) * 3 *
        (4 * X - 1) * (11 - 4 * X) := by
    simp [WPFiniteNC122Residue.Qrev,
      derivative_pow_succ, div_eq_mul_inv,Polynomial.C_ofNat]
    ring
  have ht2 : (T (-2) : K[T;T⁻¹]) = T (-1) ^ 2 := by
    rw [T_pow]
    norm_num
  rw [originalQ, D_invert, D_toLaurent, hd]
  simp only [map_mul, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    invert_C, invert_T]
  rw [ht2]
  ring

theorem originalQ_lowKernel :
    (originalQ : K[T;T⁻¹]) * lowKernel =
      (WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
        D originalQ := by
  have htu := T_one_inverse (K := K)
  have h1 :
      (4 * T 1 - 1 : K[T;T⁻¹]) * T (-1) =
        4 - T (-1) := by
    linear_combination 4 * htu
  have h2 :
      (4 - T 1 : K[T;T⁻¹]) * T (-1) =
        4 * T (-1) - 1 := by
    linear_combination -htu
  have hpairs :
      (4 * T (-1) - 1 : K[T;T⁻¹]) * (4 - T (-1)) =
        (4 - T 1) * (4 * T 1 - 1) * T (-1) ^ 2 := by
    calc
      _ = ((4 - T 1 : K[T;T⁻¹]) * T (-1)) *
          ((4 * T 1 - 1 : K[T;T⁻¹]) * T (-1)) := by rw [h2, h1]
      _ = _ := by ring
  rw [D_originalQ_factor,originalQ_factor,
    WPFiniteNC122Residue.Qrev_factored]
  simp only [map_mul, map_pow, map_sub, map_ofNat, map_one,
    Polynomial.toLaurent_C, Polynomial.toLaurent_X]
  unfold lowKernel
  calc
    _ = -3 * LaurentPolynomial.C ((125 : K)⁻¹) ^ 2 *
        (4 * T (-1) - 1) * (11 - 4 * T (-1)) *
        ((4 * T (-1) - 1) * (4 - T (-1))) *
        (4 * T 1 - 1) := by ring
    _ = -3 * LaurentPolynomial.C ((125 : K)⁻¹) ^ 2 *
        (4 * T (-1) - 1) * (11 - 4 * T (-1)) *
        ((4 - T 1) * (4 * T 1 - 1) * T (-1) ^ 2) *
        (4 * T 1 - 1) := by rw [hpairs]
    _ = _ := by ring

theorem D_substitute_originalQ (G : K[X]) :
    D (substituteOver G (originalQ : K[T;T⁻¹])) =
      substituteOver G.derivative originalQ * D originalQ := by
  change
    D (substituteOver G
      (invert (WPFiniteNC122Residue.Qrev : K[X]).toLaurent)) =
    substituteOver G.derivative
      (invert (WPFiniteNC122Residue.Qrev : K[X]).toLaurent) *
    D (invert (WPFiniteNC122Residue.Qrev : K[X]).toLaurent)
  rw [← substituteOver_invert G
    (WPFiniteNC122Residue.Qrev : K[X]).toLaurent,
    substituteOver_toLaurent]
  simp only [D_invert, D_toLaurent, derivative_comp, map_mul]
  rw [← substituteOver_toLaurent G.derivative
    (WPFiniteNC122Residue.Qrev : K[X]),
    substituteOver_invert]
  ring

theorem mul_divX_right (F E : K[X]) (hE : E.eval 0 = 0) :
    (F * E).divX = F * E.divX := by
  have he0 : E.coeff 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero] using hE
  have hfe0 : (F * E).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_mul, hE, mul_zero]
  have he : X * E.divX = E := by
    simpa only [he0, map_zero, add_zero] using X_mul_divX_add E
  apply mul_left_cancel₀ (X_ne_zero (R := K))
  calc
    X * (F * E).divX = F * E := by
      simpa only [hfe0, map_zero, add_zero] using
        X_mul_divX_add (F * E)
    _ = F * (X * E.divX) := by rw [he]
    _ = X * (F * E.divX) := by ring

theorem density_kernel (E : K[X]) :
    (WPFiniteNC122Residue.canceledDensity E).toLaurent =
      -(T 2 * lowU E) := by
  unfold WPFiniteNC122Residue.canceledDensity
  rw [map_mul,
    ← substituteOver_toLaurent E.divX
      (WPFiniteNC122Residue.Qrev : K[X]),
    Frev_laurent_kernel]
  unfold lowU
  ring

theorem density_product_kernel (F E : K[X])
    (hE : E.eval 0 = 0) :
    (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent =
      -(T 2 *
        (substituteOver F
          (WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
          lowU E)) := by
  unfold WPFiniteNC122Residue.canceledDensity
  rw [mul_divX_right F E hE, mul_comp]
  simp only [map_mul]
  rw [← substituteOver_toLaurent F
      (WPFiniteNC122Residue.Qrev : K[X]),
    ← substituteOver_toLaurent E.divX
      (WPFiniteNC122Residue.Qrev : K[X]),
    Frev_laurent_kernel]
  unfold lowU
  ring

theorem originalQ_lowU (E : K[X]) (hE : E.eval 0 = 0) :
    (originalQ : K[T;T⁻¹]) * lowU E =
      substituteOver E
        (WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
        D originalQ := by
  have he0 : E.coeff 0 = 0 := by
    simpa only [coeff_zero_eq_eval_zero] using hE
  have he : X * E.divX = E := by
    simpa only [he0, map_zero, add_zero] using X_mul_divX_add E
  have hsub :
      (WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
        substituteOver E.divX
          (WPFiniteNC122Residue.Qrev : K[X]).toLaurent =
      substituteOver E
        (WPFiniteNC122Residue.Qrev : K[X]).toLaurent := by
    have h := congrArg
      (Polynomial.eval₂RingHom LaurentPolynomial.C
        (WPFiniteNC122Residue.Qrev : K[X]).toLaurent) he
    simpa only [substituteOver, Polynomial.coe_eval₂RingHom,
      map_mul, Polynomial.eval₂_X] using h
  unfold lowU
  calc
    _ = (originalQ * lowKernel) *
        substituteOver E.divX
          (WPFiniteNC122Residue.Qrev : K[X]).toLaurent := by ring
    _ = ((WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
        D originalQ) *
        substituteOver E.divX
          (WPFiniteNC122Residue.Qrev : K[X]).toLaurent := by
      rw [originalQ_lowKernel]
    _ = ((WPFiniteNC122Residue.Qrev : K[X]).toLaurent *
        substituteOver E.divX
          (WPFiniteNC122Residue.Qrev : K[X]).toLaurent) *
        D originalQ := by ring
    _ = _ := by rw [hsub]

theorem lowU_origin (E : K[X]) (hE : E.eval 0 = 0) :
    (lowU E).coeff (-1) = -3 * E.eval (4 / 125) := by
  have hc := congrArg
    (fun L : K[T;T⁻¹] => L.coeff 1) (density_kernel E)
  have hcoeff := WPFiniteJCarrier.toLaurent_coeff_nat
    (WPFiniteNC122Residue.canceledDensity E) 1
  simp only [Nat.cast_one] at hcoeff
  rw [hcoeff,
    WPFiniteNC122Residue.canceled_density_full_coefficient E hE] at hc
  simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply] at hc
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) 2 1 (lowU E)
  simp only [map_one, one_mul,
    show (1 : ℤ) - 2 = -1 by norm_num] at hs
  rw [hs] at hc
  linear_combination hc

variable (p : ℕ) [Fact p.Prime]

noncomputable def actualF : (ZMod p)[X] :=
  quadraticInverse (actualLegendreJacobi p ^ 2)

noncomputable def actualH : (ZMod p)[X] :=
  unitEuler p (actualF p)

theorem actualF_eq_native (hp : 19 ≤ p) :
    actualF p = nativeField p (p / 6) := by
  have h := congrArg
    (fun G : (ZMod p)[X] => quadraticInverse G)
    (WPActualNativeQuadraticSquare.actual_native_Jacobi_square p hp)
  rw [quadraticInverse_quadratic] at h
  exact h.symm

theorem Qrev_eq_fieldV :
    (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) =
      WPHasseIntegralTransport.fieldV p := by
  have hc : (((1 / 125 : ℚ) : ZMod p)) = (125 : ZMod p)⁻¹ := by
    simpa only [one_div, Nat.cast_ofNat] using
      (Rat.cast_inv_nat (α := ZMod p) 125)
  rw [WPFiniteNC122Residue.Qrev_factored,
    WPHasseIntegralTransport.fieldV, hc]

theorem actualF_degree (hp : 19 ≤ p) :
    (actualF p).natDegree ≤ p / 6 := by
  rw [actualF_eq_native p hp]
  exact actual_native_field_degree p

theorem actualF_origin (hp : 19 ≤ p) :
    (actualF p).coeff 0 = 1 := by
  rw [actualF_eq_native p hp, coeff_zero_eq_eval_zero,
    actual_native_field_origin]

theorem actualH_degree (hp : 19 ≤ p) :
    (actualH p).natDegree ≤ p / 6 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hz : (actualF p).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      ((actualF_degree p hp).trans_lt hn)
  rw [actualH, unitEuler_coeff]
  simp [hz]

theorem actualEuler_source (hp : 19 ≤ p) :
    X * (actualH p).derivative = actualF p - 1 := by
  have hdeg : (actualF p).natDegree < p :=
    (actualF_degree p hp).trans_lt (by omega)
  ext n
  cases n with
  | zero =>
      simp [actualF_origin p hp]
  | succ n =>
      have hone : (1 : (ZMod p)[X]).coeff (n + 1) = 0 := by
        rw [coeff_one,if_neg (by omega : n+1≠0)]
      rw [coeff_X_mul, coeff_derivative, actualH,
        unitEuler_coeff, coeff_sub, hone, sub_zero]
      by_cases hn : n + 1 < p
      · rw [if_pos hn]
        have hu : ((n + 1 : ℕ) : ZMod p) ≠ 0 :=
          WPFiniteField.denominator_ne_zero p (n + 1)
            (Finset.mem_Ico.mpr (by omega))
        simp only [Nat.cast_add, Nat.cast_one] at hu ⊢
        field_simp [hu]
      · rw [if_neg hn,
          coeff_eq_zero_of_natDegree_lt (by omega)]
        simp

theorem actualF_whole_reciprocity (hp : 19 ≤ p) :
    substituteOver (actualF p)
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent =
      T (((p - 1) / 2 : ℕ) : ℤ) *
        substituteOver (actualF p)
          (originalQ : (ZMod p)[T;T⁻¹]) := by
  change
    substituteOver (actualF p)
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent =
    T (((p - 1) / 2 : ℕ) : ℤ) *
      substituteOver (actualF p)
        (invert (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent)
  rw [← substituteOver_invert (actualF p)
    (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent,
    substituteOver_toLaurent,
    actualF_eq_native p hp, Qrev_eq_fieldV p]
  exact WPActualHasseReciprocal.actual_native_Hasse_Laurent p (by omega)

theorem actual_originalQ_ne_zero (hp : 19 ≤ p) :
    (originalQ : (ZMod p)[T;T⁻¹]) ≠ 0 := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : ZMod p) ≠ 0 := by
    rw [show (125 : ZMod p) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  have hc :
      (originalQ : (ZMod p)[T;T⁻¹]).coeff 0 =
        (4 / 125 : ZMod p) := by
    simp only [originalQ, invert_apply, neg_zero]
    have hcoeff := WPFiniteJCarrier.toLaurent_coeff_nat
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]) 0
    simp only [Nat.cast_zero] at hcoeff
    rw [hcoeff]
    simp [WPFiniteNC122Residue.Qrev]
  intro hz
  have h := congrArg
    (fun L : (ZMod p)[T;T⁻¹] => L.coeff 0) hz
  rw [hc] at h
  have hzero : (4 / 125 : ZMod p) = 0 := by simpa using h
  exact div_ne_zero h4 h125 hzero

theorem actual_low_euler_NC87 (hp : 19 ≤ p) :
    Ij p 0 (actualF p * actualSecondLogField p) =
      (substituteOver (actualH p)
          (originalQ : (ZMod p)[T;T⁻¹]) *
        D (substituteOver (actualSecondLogField p)
          (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent)).coeff (-1) +
      3 * (actualSecondLogField p).eval (4 / 125) := by
  let F := actualF p
  let E := actualSecondLogField p
  let H := actualH p
  let Q : (ZMod p)[T;T⁻¹] := originalQ
  let V : (ZMod p)[X] := WPFiniteNC122Residue.Qrev
  let FQ := substituteOver F Q
  let HQ := substituteOver H Q
  let EV := substituteOver E V.toLaurent
  let U := lowU E
  let N : ℤ := (((p - 1) / 2 : ℕ) : ℤ)
  change Ij p 0 (F * E) =
    (HQ * D EV).coeff (-1) + 3 * E.eval (4 / 125)
  have hE : E.eval 0 = 0 :=
    WPFieldAssembly.ActualBalancedCarry.actual_second_log_origin p
  have hQU : Q * U = EV * D Q :=
    originalQ_lowU E hE
  have heval :
      Q * substituteOver H.derivative Q = FQ - 1 := by
    have h := congrArg
      (Polynomial.eval₂RingHom LaurentPolynomial.C Q)
      (actualEuler_source p hp)
    simpa only [map_mul, map_sub, map_one,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      substituteOver, FQ, F, H] using h
  have hEulerQ : Q * D HQ = (FQ - 1) * D Q := by
    calc
      _ = Q * (substituteOver H.derivative Q * D Q) := by
        rw [D_substitute_originalQ]
      _ = (Q * substituteOver H.derivative Q) * D Q := by ring
      _ = _ := by rw [heval]
  have hFU : FQ * U = EV * D HQ + U := by
    apply mul_left_cancel₀ (actual_originalQ_ne_zero p hp)
    calc
      Q * (FQ * U) = FQ * (Q * U) := by ring
      _ = FQ * (EV * D Q) := by rw [hQU]
      _ = EV * ((FQ - 1) * D Q) + EV * D Q := by ring
      _ = EV * (Q * D HQ) + Q * U := by rw [hEulerQ, hQU]
      _ = Q * (EV * D HQ + U) := by ring
  have hshift :
      Ij p 0 (F * E) =
        (T (-N) *
          (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent).coeff 1 := by
    have h := WPFiniteJCarrier.shifted_coeff
      (1 : ZMod p) (-N) 1
      (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent
    simp only [map_one, one_mul] at h
    have hi :
        (1 : ℤ) - -N =
          (((p - 1) / 2 + 1 : ℕ) : ℤ) := by
      dsimp [N]
      omega
    rw [hi, WPFiniteJCarrier.toLaurent_coeff_nat] at h
    simpa only [Ij, Nat.zero_mul, Nat.add_zero] using h.symm
  have ht : (T (-N) : (ZMod p)[T;T⁻¹]) * T N = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hscaled :
      T (-N) *
        (WPFiniteNC122Residue.canceledDensity (F * E)).toLaurent =
      -(T 2 * (FQ * U)) := by
    rw [density_product_kernel F E hE,
      actualF_whole_reciprocity p hp]
    calc
      _ = -(T 2 * ((T (-N) * T N) * (FQ * U))) := by ring
      _ = _ := by rw [ht, one_mul]
  have hprojection :
      Ij p 0 (F * E) = -(FQ * U).coeff (-1) := by
    rw [hshift, hscaled]
    simp only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
    have h := WPFiniteJCarrier.shifted_coeff
      (1 : ZMod p) 2 1 (FQ * U)
    simpa only [map_one, one_mul,
      show (1 : ℤ) - 2 = -1 by norm_num] using
      congrArg Neg.neg h
  have hDzero : (D (HQ * EV)).coeff (-1) = 0 := by
    rw [D_coeff]
    norm_num
  rw [D_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hDzero
  have hibp :
      -(EV * D HQ).coeff (-1) = (HQ * D EV).coeff (-1) := by
    have h :
        (EV * D HQ).coeff (-1) +
          (HQ * D EV).coeff (-1) = 0 := by
      simpa only [mul_comm] using hDzero
    linear_combination -h
  calc
    Ij p 0 (F * E) = -(FQ * U).coeff (-1) := hprojection
    _ = -((EV * D HQ).coeff (-1) + U.coeff (-1)) := by
      rw [hFU, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    _ = -(EV * D HQ).coeff (-1) + 3 * E.eval (4 / 125) := by
      rw [lowU_origin E hE]
      ring
    _ = _ := by rw [hibp]

theorem actual_second_log_QO_NC87 (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p ^ 2 *
      (actualSecondLogField p).comp (1 - X ^ 2)) =
      (substituteOver (actualH p)
          (originalQ : (ZMod p)[T;T⁻¹]) *
        D (substituteOver (actualSecondLogField p)
          (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent)).coeff (-1) +
      3 * (actualSecondLogField p).eval (4 / 125) := by
  have hs :
      (actualF p).comp (1 - X ^ 2) =
        actualLegendreJacobi p ^ 2 := by
    rw [actualF_eq_native p hp]
    exact WPActualNativeQuadraticSquare.actual_native_Jacobi_square p hp
  have hi :
      quadraticInverse
        (actualLegendreJacobi p ^ 2 *
          (actualSecondLogField p).comp (1 - X ^ 2)) =
      actualF p * actualSecondLogField p := by
    rw [← hs, ← mul_comp, quadraticInverse_quadratic]
  rw [QO, hi]
  exact actual_low_euler_NC87 p hp

theorem actual_logPairIntegral_NC87 (hp : 19 ≤ p) :
    residueHom p
      (WPFieldAssembly.ActualBalancedCarry.logPairIntegral p hp) =
      (substituteOver (actualH p)
          (originalQ : (ZMod p)[T;T⁻¹]) *
        D (substituteOver (actualSecondLogField p)
          (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent)).coeff (-1) +
      3 * (actualSecondLogField p).eval (4 / 125) := by
  rw [WPFieldAssembly.ActualBalancedCarry.logPairIntegral_field]
  exact actual_second_log_QO_NC87 p hp

theorem laurent_low_contraction
    (A B : K[X]) (L : ℕ) (hA : A.natDegree ≤ L) :
    (invert A.toLaurent * B.derivative.toLaurent).coeff (-1) =
      ∑ j ∈ Finset.range (L + 1),
        (j : K) * A.coeff j * B.coeff j := by
  classical
  conv_lhs =>
    rw [Polynomial.as_sum_range' A (L + 1) (by omega)]
  simp only [map_sum, Finset.sum_mul,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.toLaurent_C_mul_T,
    map_mul, invert_C, invert_T]
  rw [← D_toLaurent B, WPFiniteJCarrier.shifted_coeff, D_coeff]
  have hi : (-1 : ℤ) - -(j : ℤ) + 1 = (j : ℤ) := by omega
  rw [hi, WPFiniteJCarrier.toLaurent_coeff_nat]
  simp only [Int.cast_natCast]
  ring

theorem actualH_pullback_degree (hp : 19 ≤ p) :
    ((actualH p).comp
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).natDegree ≤
        3 * (p / 6) := by
  have hV :
      (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).natDegree ≤ 3 := by
    unfold WPFiniteNC122Residue.Qrev
    compute_degree
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul (actualH_degree p hp) hV).trans (by omega))

theorem actual_low_euler_index_unit (_hp : 19 ≤ p)
    (j : ℕ) (hj0 : 0 < j) (hj : j ≤ 3 * (p / 6)) :
    (j : ZMod p) ≠ 0 :=
  WPFiniteField.denominator_ne_zero p j
    (Finset.mem_Ico.mpr (by omega))

theorem actual_logPairIntegral_SB70 (hp : 19 ≤ p) :
    residueHom p
      (WPFieldAssembly.ActualBalancedCarry.logPairIntegral p hp) =
      (∑ j ∈ Finset.range (3 * (p / 6) + 1),
        (j : ZMod p) *
          ((actualH p).comp
            (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).coeff j *
          ((actualSecondLogField p).comp
            (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).coeff j) +
      3 * (actualSecondLogField p).eval (4 / 125) := by
  have hH :
      substituteOver (actualH p)
        (originalQ : (ZMod p)[T;T⁻¹]) =
      invert (((actualH p).comp
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).toLaurent) := by
    change substituteOver (actualH p)
      (invert (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent) = _
    rw [← substituteOver_invert, substituteOver_toLaurent]
  have hE :
      D (substituteOver (actualSecondLogField p)
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X]).toLaurent) =
      ((actualSecondLogField p).comp
        (WPFiniteNC122Residue.Qrev : (ZMod p)[X])).derivative.toLaurent := by
    rw [substituteOver_toLaurent, D_toLaurent]
  rw [actual_logPairIntegral_NC87 p hp, hH, hE,
    laurent_low_contraction _ _ (3 * (p / 6))
      (actualH_pullback_degree p hp)]

end WPFieldAssembly.ActualLowEuler
