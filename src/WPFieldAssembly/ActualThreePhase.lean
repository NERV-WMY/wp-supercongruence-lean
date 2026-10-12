import WPFieldAssembly.ActualConicDescent
import WPFieldAssembly.ActualFirstGreen
import WPFieldAssembly.ActualChiEndpoints
import WPFiniteZSupport
import WPActualNativeDegree

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteLaurentDifferential WPFiniteWSource WPFinitePSource
  WPFiniteABSourceTail WPFiniteZSupport WPFiniteLVSharp WPActualRankTwoLegendreField
  WPActualRankTwoProper WPActualNativeDegree WPFiniteCubicLog
  WPFieldAssembly.ConicCoefficients WPFieldAssembly.ConicKernel
  WPFieldAssembly.ActualConicProper WPFieldAssembly.ActualConicSource
  WPFieldAssembly.ActualConicDescent WPFieldAssembly.NativeShiftedChi
  WPFieldAssembly.NativeChiFieldSource
open LaurentPolynomial (T)

namespace WPFieldAssembly.ActualThreePhase

set_option maxHeartbeats 1600000

variable {K : Type*} [Field K]

noncomputable def φ (p : ℕ) [Fact p.Prime] [CharP K p] :
    ZMod p →+* K := ZMod.castHom (dvd_refl p) K

noncomputable def fK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] := (halfPullbackField p hp).map (φ (K := K) p)

noncomputable def HK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[X] := (shiftedChiField p hp).map (φ (K := K) p)

noncomputable def CBK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (ActualFirstGreen.CB p).map (φ (K := K) p)

noncomputable def χK (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : K[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (φ (K := K) p) (halfChiField p hp)

noncomputable def yK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  ((actualLegendreJacobi p).comp Tc).map (φ (K := K) p)

noncomputable def mK (p : ℕ) [Fact p.Prime] [CharP K p] : K[X] :=
  (C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc).map (φ (K := K) p)

noncomputable def Gx (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) : K[X] :=
  HK (K := K) p hp - fK (K := K) p hp * Pnumerator p u -
    C (1 / 3 : K) * WPFiniteZSource.Abar ^ p * CBK (K := K) p

private theorem B_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (B : K[X]).natDegree = 2 := by
  have h5 : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega))
  apply le_antisymm
  · unfold B
    compute_degree
  · apply le_natDegree_of_ne_zero
    simpa [B, coeff_one, coeff_X_pow, coeff_X] using h5

private theorem cubic_degree (p : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) : (Tc : (ZMod p)[X]).natDegree = 3 := by
  have h4 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  apply le_antisymm
  · unfold Tc
    compute_degree
  · apply le_natDegree_of_ne_zero
    simpa [Tc, coeff_X_pow, coeff_X] using h4

private theorem map_B (p : ℕ) [Fact p.Prime] [CharP K p] :
    (B : (ZMod p)[X]).map (φ (K := K) p) = (B : K[X]) := by
  simp [B]

private theorem map_Abar (p : ℕ) [Fact p.Prime] [CharP K p] :
    (WPFiniteZSource.Abar : (ZMod p)[X]).map (φ (K := K) p) =
      (WPFiniteZSource.Abar : K[X]) := by
  simp [WPFiniteZSource.Abar]

private theorem map_S (p : ℕ) [Fact p.Prime] [CharP K p] :
    (squaredCoordinate : (ZMod p)[X]).map (φ (K := K) p) =
      (squaredCoordinate : K[X]) := by
  simp only [squaredCoordinate, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_one, map_inv₀]
  have h5 : φ (K := K) p (5 : ZMod p) = (5 : K) := by
    simpa only [Nat.cast_ofNat] using (map_natCast (φ (K := K) p) 5)
  rw [h5]

private theorem map_conicA (p : ℕ) [Fact p.Prime] [CharP K p] :
    (conicA : (ZMod p)[X]).map (φ (K := K) p) = (conicA : K[X]) := by
  simp [conicA]

private theorem C_unit (n : ℕ) (hn : (n : K) ≠ 0) :
    (n : K[X]) * C (1 / (n : K)) = 1 := by
  change C (n : K) * C (1 / (n : K)) = C 1
  rw [← map_mul, mul_one_div_cancel hn]

theorem HK_toLaurent (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (HK (K := K) p hp).toLaurent = T (p : ℤ) * χK (K := K) p hp := by
  have he := congrArg (WPActualChiSource.coefficientMap (φ (K := K) p))
    (shiftedChiField_toLaurent p hp)
  simpa only [HK, χK, halfChiField, map_mul,
    WPActualChiSource.coefficientMap_toLaurent,
    WPActualChiSource.coefficientMap_T] using he

private theorem map_comp_square
    {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (P Q B0 : R[X]) (B1 : S[X])
    (hB : B0.map ψ = B1)
    (h : P.comp B0 = Q ^ 2) :
    (P.map ψ).comp B1 = (Q.map ψ) ^ 2 := by
  calc
    (P.map ψ).comp B1 = (P.map ψ).comp (B0.map ψ) :=
      congrArg (fun A : S[X] => (P.map ψ).comp A) hB.symm
    _ = (P.comp B0).map ψ := (Polynomial.map_comp ψ P B0).symm
    _ = (Q ^ 2).map ψ := congrArg (fun A : R[X] => A.map ψ) h
    _ = (Q.map ψ) ^ 2 := Polynomial.map_pow ψ (p := Q) 2

theorem actual_f_conic (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (fK (K := K) p hp).comp B = yK (K := K) p ^ 2 := by
  have hz : (halfPullbackField p hp).comp B =
      ((actualLegendreJacobi p).comp Tc) ^ 2 := by
    rw [halfPullbackField_eq]
    exact actual_full_native_conic_square p hp
  change ((halfPullbackField p hp).map (φ (K := K) p)).comp (B : K[X]) =
    (((actualLegendreJacobi p).comp Tc).map (φ (K := K) p)) ^ 2
  exact map_comp_square (φ (K := K) p) (halfPullbackField p hp)
    ((actualLegendreJacobi p).comp Tc) (B : (ZMod p)[X]) (B : K[X])
    (map_B (K := K) p) hz

private theorem map_Wronskian
    {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (a y m : R[X]) (a' : S[X])
    (ha : a.map ψ = a')
    (h : a * (y * m.derivative - y.derivative * m) = 1 - y ^ 2) :
    a' * (y.map ψ * (m.map ψ).derivative -
      (y.map ψ).derivative * m.map ψ) = 1 - (y.map ψ) ^ 2 := by
  have he := congrArg (fun P : R[X] => P.map ψ) h
  simpa only [Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, ← derivative_map, ha] using he

theorem actual_m_Wronskian (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    conicA * (yK (K := K) p * (mK (K := K) p).derivative -
      (yK (K := K) p).derivative * mK (K := K) p) = 1 - yK (K := K) p ^ 2 := by
  change conicA *
    ((((actualLegendreJacobi p).comp Tc).map (φ (K := K) p)) *
      ((C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc).map
        (φ (K := K) p)).derivative -
      (((actualLegendreJacobi p).comp Tc).map (φ (K := K) p)).derivative *
        ((C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc).map
          (φ (K := K) p))) =
    1 - (((actualLegendreJacobi p).comp Tc).map (φ (K := K) p)) ^ 2
  exact map_Wronskian (φ (K := K) p) conicA
    ((actualLegendreJacobi p).comp Tc)
    (C (1 / 3 : ZMod p) * (properLegendreJacobi p).comp Tc)
    (conicA : K[X]) (map_conicA (K := K) p)
    (actual_conic_proper_wronskian p hp)

theorem actual_y_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (yK (K := K) p).natDegree = 3 * (p / 6) := by
  rw [yK, natDegree_map_eq_of_injective (φ (K := K) p).injective,
    natDegree_comp, actualLegendreJacobi_exact_degree p hp,
    cubic_degree p hp]
  omega

theorem actual_CB_pullback (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (CBK (K := K) p).comp B = (ActualFirstGreen.CBt p).map (φ (K := K) p) := by
  have hz := (ActualFirstGreen.actual_carrier_pullbacks p hp).1
  change (ActualFirstGreen.CB p).comp B = ActualFirstGreen.CBt p at hz
  have he := congrArg (fun P : (ZMod p)[X] => P.map (φ (K := K) p)) hz
  simpa only [CBK, Polynomial.map_comp, map_B] using he

/-- The canonical CB source is derived from the actual proper Wronskian. -/
theorem actual_CB_Wronskian_ZMod (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    let f := halfPullbackField p hp
    2 * WPFiniteZSource.Abar *
      (f * (ActualFirstGreen.CB p).derivative -
        f.derivative * ActualFirstGreen.CB p) =
      3 * squaredCoordinate ^ ((p - 1) / 2) * f * (1 - f) := by
  let y := (actualLegendreJacobi p).comp Tc
  let n := (properLegendreJacobi p).comp Tc
  let f := halfPullbackField p hp
  have h3 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hu3 := C_unit (K := ZMod p) 3 h3
  have hu5 := C_unit (K := ZMod p) 5 h5
  simp only [Nat.cast_ofNat] at hu3 hu5
  have hF : f.comp B = y ^ 2 := by
    change (halfPullbackField p hp).comp B = _
    rw [halfPullbackField_eq]
    exact actual_full_native_conic_square p hp
  have hCB := (ActualFirstGreen.actual_carrier_pullbacks p hp).1
  change (ActualFirstGreen.CB p).comp B = ActualFirstGreen.CBt p at hCB
  have ht : ActualFirstGreen.CBt p =
      C (1 / 5 : ZMod p) * X ^ p * (y * n) := by
    simp only [ActualFirstGreen.CBt, ActualFirstGreen.B, mul_comp]
    rfl
  have hw := actual_conic_proper_wronskian p hp
  change conicA * (y * (C (1 / 3 : ZMod p) * n).derivative -
      y.derivative * (C (1 / 3 : ZMod p) * n)) = 1 - y ^ 2 at hw
  simp only [derivative_C_mul] at hw
  have hn : conicA * (y * n.derivative - y.derivative * n) =
      3 * (1 - y ^ 2) := by
    linear_combination
      3 * hw - conicA * (y * n.derivative - y.derivative * n) * hu3
  have hd : (X ^ p : (ZMod p)[X]).derivative = 0 := by
    simp [derivative_X_pow]
  have htW :
      5 * conicA *
        (y ^ 2 * (ActualFirstGreen.CBt p).derivative -
          (y ^ 2).derivative * ActualFirstGreen.CBt p) =
        3 * X ^ p * y ^ 2 * (1 - y ^ 2) := by
    calc
      _ = (5 * C (1 / 5 : ZMod p)) * X ^ p * y ^ 2 *
          (conicA * (y * n.derivative - y.derivative * n)) := by
        rw [ht]
        simp only [derivative_mul, derivative_C, hd, derivative_sq,
          C_ofNat, zero_mul, zero_add]
        ring
      _ = _ := by rw [hu5, one_mul, hn]; ring
  let E : (ZMod p)[X] :=
    2 * WPFiniteZSource.Abar *
      (f * (ActualFirstGreen.CB p).derivative -
        f.derivative * ActualFirstGreen.CB p) -
      3 * squaredCoordinate ^ ((p - 1) / 2) * f * (1 - f)
  have h2N : 2 * ((p - 1) / 2) = p - 1 := by
    have := half_exponent p hp
    omega
  have hXp : (X : (ZMod p)[X]) * X ^ (p - 1) = X ^ p := by
    rw [← pow_succ', show p - 1 + 1 = p by omega]
  have hz : X * E.comp B = 0 := by
    calc
      _ = 5 * conicA *
          ((f.comp B) * ((ActualFirstGreen.CB p).comp B).derivative -
            (f.comp B).derivative * (ActualFirstGreen.CB p).comp B) -
          3 * X ^ p * f.comp B * (1 - f.comp B) := by
        dsimp only [E]
        simp only [mul_comp, sub_comp, pow_comp, ofNat_comp, one_comp,
          derivative_comp, B_derivative, Abar_conic,
          ActualConicDescent.squaredCoordinate_conic p hp]
        rw [← pow_mul, h2N]
        linear_combination -3 * f.comp B * (1 - f.comp B) * hXp
      _ = 0 := by rw [hF, hCB]; exact sub_eq_zero.mpr htW
  have hEc : E.comp B = 0 := (mul_eq_zero.mp hz).resolve_left X_ne_zero
  have hE : E = 0 := comp_injective_nonconstant B
    (by rw [B_degree (K := ZMod p) p hp]; omega)
    (by simpa only [zero_comp] using hEc)
  exact sub_eq_zero.mp hE

theorem actual_CB_Wronskian (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    2 * WPFiniteZSource.Abar *
      (fK (K := K) p hp * (CBK (K := K) p).derivative -
        (fK (K := K) p hp).derivative * CBK (K := K) p) =
      3 * squaredCoordinate ^ ((p - 1) / 2) * fK (K := K) p hp * (1 - fK (K := K) p hp) := by
  have he := congrArg (fun P : (ZMod p)[X] => P.map (φ (K := K) p))
    (actual_CB_Wronskian_ZMod p hp)
  simpa only [fK, CBK, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_one, Polynomial.map_ofNat,
    ← derivative_map, map_Abar, map_S] using he

/-- Polynomial clearing of the retained, unconditional finite P derivative. -/
theorem actual_Pnumerator_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Pnumerator p u).derivative =
      C (1 / 2 : K) *
        (WPFiniteZSource.Abar ^ (p - 1) *
          squaredCoordinate ^ ((p - 1) / 2) - X ^ (p - 1)) := by
  apply Polynomial.toLaurent_injective
  have hd : (Pnumerator p u).derivative.toLaurent =
      T (p : ℤ) * D (WPFiniteZSource.P p u) := by
    rw [← D_toLaurent, ← WPFiniteZSource.P_numerator,
      D_frobenius_shift p _ _ (dvd_refl _)]
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  have ht1 : (T (p : ℤ) * T (-1) : K[T;T⁻¹]) =
      T ((p - 1 : ℕ) : ℤ) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  rw [hd, WPFiniteZSource.P_derivative p hp u]
  simp only [map_mul, map_sub, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one]
  unfold WPFiniteZSource.R
  linear_combination
    LaurentPolynomial.C (1 / 2 : K) *
      WPFiniteZSource.Abar.toLaurent ^ (p - 1) *
      squaredCoordinate.toLaurent ^ ((p - 1) / 2) * ht -
    LaurentPolynomial.C (1 / 2 : K) * ht1

theorem actual_Gx_Wronskian (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    fK (K := K) p hp * (Gx p hp u).derivative -
      (fK (K := K) p hp).derivative * Gx p hp u = 0 := by
  have h2 : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 6 (Finset.mem_Ico.mpr (by omega))
  have hH := congrArg (fun P : (ZMod p)[X] => P.map (φ (K := K) p))
    (actual_half_chi_polynomial_Wronskian p hp)
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_ofNat, Polynomial.map_X, ← derivative_map, map_Abar, map_S] at hH
  change 2 * (fK (K := K) p hp * (HK (K := K) p hp).derivative -
      (fK (K := K) p hp).derivative * HK (K := K) p hp) =
    WPFiniteZSource.Abar ^ (p - 1) *
      squaredCoordinate ^ ((p - 1) / 2) * fK (K := K) p hp -
      X ^ (p - 1) * (fK (K := K) p hp) ^ 2 at hH
  have hP := actual_Pnumerator_source p hp u
  have hu2 := C_unit (K := K) 2 h2
  simp only [Nat.cast_ofNat] at hu2
  have hP2 : 2 * (Pnumerator p u).derivative =
      WPFiniteZSource.Abar ^ (p - 1) *
        squaredCoordinate ^ ((p - 1) / 2) - X ^ (p - 1) := by
    linear_combination
      2 * hP +
      (WPFiniteZSource.Abar ^ (p - 1) *
        squaredCoordinate ^ ((p - 1) / 2) - X ^ (p - 1)) * hu2
  have hCB := actual_CB_Wronskian (K := K) p hp
  have hAp : ((WPFiniteZSource.Abar : K[X]) ^ p).derivative = 0 := by
    simp [derivative_pow]
  have hpow : (WPFiniteZSource.Abar : K[X]) ^ (p - 1) *
      WPFiniteZSource.Abar = WPFiniteZSource.Abar ^ p := by
    rw [← pow_succ, show p - 1 + 1 = p by omega]
  have hz :
      (6 * WPFiniteZSource.Abar : K[X]) *
        (fK (K := K) p hp * (Gx p hp u).derivative -
          (fK (K := K) p hp).derivative * Gx p hp u) = 0 := by
    dsimp only [Gx]
    simp only [derivative_sub, derivative_mul, derivative_C,
      hAp, zero_mul, zero_add]
    simp only [← hpow]
    linear_combination
      3 * WPFiniteZSource.Abar * hH -
      3 * WPFiniteZSource.Abar * (fK (K := K) p hp) ^ 2 * hP2 -
      (WPFiniteZSource.Abar ^ (p - 1) * WPFiniteZSource.Abar) * hCB -
      2 * WPFiniteZSource.Abar *
        (WPFiniteZSource.Abar ^ (p - 1) * WPFiniteZSource.Abar) *
        (fK (K := K) p hp * (CBK (K := K) p).derivative -
          (fK (K := K) p hp).derivative * CBK (K := K) p) * C_unit 3 h3
  have hA : (WPFiniteZSource.Abar : K[X]) ≠ 0 := by
    intro he
    have hc : (-4 : K) = 0 := by
      simpa [WPFiniteZSource.Abar] using
        congrArg (fun P : K[X] => P.eval 0) he
    exact (neg_ne_zero.mpr h4) hc
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero (C_ne_zero.mpr h6) hA)

private theorem Pnumerator_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Pnumerator p u).natDegree ≤ 2 * p + (p - 1) / 2 - 1 := by
  have hA := A_degree (K := K) p hp u
  have hB := (original_phase_degrees (K := K) p hp u).1
  have hC := (original_phase_degrees (K := K) p hp u).2
  have h1 : (X ^ (2 * p) * A p (W p) u : K[X]).natDegree ≤
      2 * p + (p - 1) / 2 - 1 :=
    (natDegree_mul_le_of_le
      (show (X ^ (2 * p) : K[X]).natDegree ≤ 2 * p by simp) hA).trans (by omega)
  have h2 : (X ^ p * B0 p (W p) u : K[X]).natDegree ≤
      2 * p + (p - 1) / 2 - 1 :=
    (natDegree_mul_le_of_le
      (show (X ^ p : K[X]).natDegree ≤ p by simp) hB).trans (by omega)
  have h3 : (Cminus p u : K[X]).natDegree ≤
      2 * p + (p - 1) / 2 - 1 := hC.trans (by omega)
  unfold Pnumerator
  exact (natDegree_add_le _ _).trans
    (max_le ((natDegree_add_le _ _).trans (max_le h1 h2)) h3)

/-- Actual square divisibility, with its complete bounded homogeneous kernel. -/
theorem actual_Gx_kernel (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ∃ b : K[X], (Gx p hp u).comp B = yK (K := K) p ^ 2 * b ∧
      b.derivative = 0 ∧ b.comp (-X) = b ∧ b.natDegree ≤ 5 * p - 3 := by
  let d := p / 6
  let F := (fK (K := K) p hp).comp B
  let M := (Gx p hp u).comp B
  have hF := actual_f_conic (K := K) p hp
  have hyn := actual_y_degree (K := K) p hp
  have hy : yK (K := K) p ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hyn
    omega
  have hFn : F.natDegree = 6 * d := by
    dsimp only [F, d]
    rw [hF, natDegree_pow, hyn]
    omega
  have hFnz : F ≠ 0 := by
    dsimp only [F]
    rw [hF]
    exact pow_ne_zero 2 hy
  have hWM : F * M.derivative - F.derivative * M = 0 := by
    have he := congrArg (fun P : K[X] => P.comp B)
      (actual_Gx_Wronskian p hp u)
    simp only [mul_comp, sub_comp, zero_comp] at he
    dsimp only [F, M]
    simp only [derivative_comp]
    linear_combination B.derivative * he
  have hsource :
      M.derivative * yK (K := K) p - 2 * M * (yK (K := K) p).derivative = 0 := by
    have hz : yK (K := K) p *
        (M.derivative * yK (K := K) p - 2 * M * (yK (K := K) p).derivative) = 0 := by
      dsimp only [F] at hWM
      rw [hF] at hWM
      simp only [derivative_sq, C_ofNat] at hWM
      linear_combination hWM
    exact (mul_eq_zero.mp hz).resolve_left hy
  have h2 : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  obtain ⟨b, hb, hDb⟩ := WPActualNativeJacobiJet.proper_square_division
    (1 / 2 : K) (mul_one_div_cancel h2) conicA (yK (K := K) p) (mK (K := K) p) M hy
    (actual_m_Wronskian p hp) hsource
  have hbF : M = F * b := by
    dsimp only [F]
    rw [hF]
    exact hb
  have hBneg : (B : K[X]).comp (-X) = B := by
    simp only [B, sub_comp, mul_comp, pow_comp, ofNat_comp, X_comp, one_comp]
    ring
  have even_pull (P : K[X]) : (P.comp B).comp (-X) = P.comp B := by
    rw [comp_assoc, hBneg]
  have hev : b.comp (-X) = b := by
    apply mul_left_cancel₀ hFnz
    calc
      F * b.comp (-X) = (F * b).comp (-X) := by
        rw [mul_comp]
        exact congrArg (fun Q : K[X] => Q * b.comp (-X))
          (even_pull (fK (K := K) p hp)).symm
      _ = M.comp (-X) := by rw [← hbF]
      _ = M := even_pull (Gx p hp u)
      _ = F * b := hbF
  have hN : 2 * ((p - 1) / 2) = p - 1 := by
    have := half_exponent p hp
    omega
  have hBdeg := (B_degree (K := K) p hp).le
  have hHdeg : ((HK (K := K) p hp).comp B).natDegree ≤ 5 * p - 3 := by
    have hh : (HK (K := K) p hp).natDegree ≤ p + 3 * ((p - 1) / 2) :=
      natDegree_map_le.trans (shiftedChiField_degree p hp)
    exact ((natDegree_comp_le (p := HK (K := K) p hp) (q := B)).trans
      (Nat.mul_le_mul hh hBdeg)).trans (by omega)
  have hPdeg : ((Pnumerator p u).comp B).natDegree ≤ 5 * p - 3 :=
    ((natDegree_comp_le (p := Pnumerator p u) (q := B)).trans
      (Nat.mul_le_mul (Pnumerator_degree p hp u) hBdeg)).trans (by omega)
  have hCBdeg : ((CBK (K := K) p).comp B).natDegree ≤ p + 6 * d - 3 := by
    rw [actual_CB_pullback p hp]
    apply natDegree_map_le.trans
    have hn : (properLegendreJacobi p).natDegree ≤ d - 1 := by
      have hh := properLegendreJacobi_degree p (by omega : 7 ≤ p)
      dsimp only [d]
      omega
    have hpB := natDegree_mul_le_of_le
      (WPActualRankTwoComparison.actualLegendreJacobi_degree p) hn
    have hpBc := (natDegree_comp_le
      (p := actualLegendreJacobi p * properLegendreJacobi p)
      (q := Tc)).trans (Nat.mul_le_mul hpB (cubic_degree p hp).le)
    have hXp : (C (1 / 5 : ZMod p) * X ^ p).natDegree ≤ p :=
      (natDegree_C_mul_le _ _).trans (by simp)
    change
      (C (1 / 5 : ZMod p) * X ^ p *
        (actualLegendreJacobi p * properLegendreJacobi p).comp Tc).natDegree ≤ _
    exact (natDegree_mul_le_of_le hXp hpBc).trans (by dsimp only [d] at *; omega)
  have hAdeg : ((WPFiniteZSource.Abar : K[X]).comp B).natDegree ≤ 4 :=
    ((natDegree_comp_le (p := WPFiniteZSource.Abar) (q := B)).trans
      (Nat.mul_le_mul pole_degree hBdeg)).trans (by omega)
  have hFP : (((fK (K := K) p hp) * Pnumerator p u).comp B).natDegree ≤
      6 * d + 5 * p - 3 := by
    rw [mul_comp]
    exact (natDegree_mul_le_of_le hFn.le hPdeg).trans (by omega)
  have hCBterm :
      ((C (1 / 3 : K) * WPFiniteZSource.Abar ^ p * CBK (K := K) p).comp B).natDegree ≤
        6 * d + 5 * p - 3 := by
    simp only [mul_comp, C_comp, pow_comp]
    have ha := natDegree_pow_le_of_le p hAdeg
    have hc : (C (1 / 3 : K) * ((WPFiniteZSource.Abar : K[X]).comp B) ^ p).natDegree ≤ p * 4 :=
      (natDegree_C_mul_le _ _).trans ha
    exact (natDegree_mul_le_of_le hc hCBdeg).trans (by omega)
  have hMdeg : M.natDegree ≤ 6 * d + 5 * p - 3 := by
    have hh := hHdeg.trans (by omega : 5 * p - 3 ≤ 6 * d + 5 * p - 3)
    dsimp only [M, Gx]
    simp only [sub_comp]
    exact (natDegree_sub_le _ _).trans
      (max_le ((natDegree_sub_le _ _).trans (max_le hh hFP)) hCBterm)
  have hbdeg : b.natDegree ≤ 5 * p - 3 := by
    by_cases hb0 : b = 0
    · simp [hb0]
    · rw [hbF, natDegree_mul hFnz hb0, hFn] at hMdeg
      omega
  exact ⟨b, hb, hDb, hev, hbdeg⟩

/-- Extension-field form of the retained three-slot derivative-kernel lemma. -/
theorem even_flat_three_slots_field (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (b : K[X]) (hD : b.derivative = 0)
    (hdeg : b.natDegree ≤ 5 * p - 3) (hev : b.comp (-X) = b) :
    ∃ a0 a2 a4 : K, b = C a0 + C a2 * X ^ (2 * p) + C a4 * X ^ (4 * p) := by
  let U := contract p b
  have hpP : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have he : expand K p U = b := Polynomial.expand_contract p hD hpP.ne_zero
  have hUd : U.natDegree ≤ 4 := by
    have hm : U.natDegree * p ≤ 5 * p - 3 := by
      rw [← natDegree_expand p U, he]
      exact hdeg
    by_contra hn
    have hh := Nat.mul_le_mul_right p (show 5 ≤ U.natDegree by omega)
    omega
  have ho : Odd p := hpP.odd_of_ne_two (by omega)
  have odd_coeff (n : ℕ) (hs : (-1 : K) ^ (n * p) = -1) :
      U.coeff n = 0 := by
    have hc := congrArg (fun Q : K[X] => Q.coeff (n * p)) hev
    rw [coeff_comp_neg, hs] at hc
    have hz : (2 : K) * b.coeff (n * p) = 0 := by linear_combination -hc
    change (contract p b).coeff n = 0
    rw [coeff_contract hpP.ne_zero]
    exact (mul_eq_zero.mp hz).resolve_left h2
  have hU1 : U.coeff 1 = 0 := odd_coeff 1 (by simpa using ho.neg_one_pow)
  have hU3 : U.coeff 3 = 0 := odd_coeff 3 (by
    rw [Nat.mul_comm, pow_mul, ho.neg_one_pow]
    norm_num)
  have hs : U = C (U.coeff 0) + C (U.coeff 2) * X ^ 2 +
      C (U.coeff 4) * X ^ 4 := by
    ext n
    by_cases hn : n ≤ 4
    · interval_cases n <;> simp [hU1, hU3]
    · have hz : U.coeff n = 0 := coeff_eq_zero_of_natDegree_lt
        (show U.natDegree < n by omega)
      have hn0 : n ≠ 0 := by omega
      have hn2 : n ≠ 2 := by omega
      have hn4 : n ≠ 4 := by omega
      simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X_pow, if_neg hn0,
        if_neg hn2, if_neg hn4, mul_zero, add_zero, hz]
  refine ⟨U.coeff 0, U.coeff 2, U.coeff 4, ?_⟩
  calc
    b = expand K p U := he.symm
    _ = expand K p (C (U.coeff 0) + C (U.coeff 2) * X ^ 2 +
        C (U.coeff 4) * X ^ 4) := congrArg (expand K p) hs
    _ = _ := by
      simp only [map_add, map_mul, map_pow, expand_C, expand_X]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm p 2, Nat.mul_comm p 4]

theorem actual_polynomial_three_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ∃ α β γ : K,
      HK (K := K) p hp = fK (K := K) p hp *
        (Pnumerator p u + C α * X ^ (2 * p) + C β * X ^ p + C γ) +
        C (1 / 3 : K) * WPFiniteZSource.Abar ^ p * CBK (K := K) p := by
  obtain ⟨b, hb, hDb, hev, hbdeg⟩ := actual_Gx_kernel (K := K) p hp u
  obtain ⟨a0, a2, a4, hslots⟩ :=
    even_flat_three_slots_field p hp b hDb hbdeg hev
  let Q : K[X] := C a0 + C a2 * squaredCoordinate ^ p +
    C a4 * squaredCoordinate ^ (2 * p)
  have hS : (squaredCoordinate : K[X]).comp B = X ^ 2 := by
    have he := congrArg (fun P : (ZMod p)[X] => P.map (φ (K := K) p))
      (ActualConicDescent.squaredCoordinate_conic p hp)
    simpa only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
      map_S, map_B] using he
  have hQpull : Q.comp B = b := by
    dsimp only [Q]
    simp only [add_comp, mul_comp, pow_comp, C_comp, hS]
    rw [← pow_mul, ← pow_mul, show 2 * (2 * p) = 4 * p by omega]
    exact hslots.symm
  have hG : Gx p hp u = fK (K := K) p hp * Q := by
    apply comp_injective_nonconstant B
      (by rw [B_degree (K := K) p hp]; omega)
    change (Gx p hp u).comp B = (fK (K := K) p hp * Q).comp B
    rw [mul_comp, hQpull, actual_f_conic p hp]
    exact hb
  let v : K := 1 / 5
  let α := a4 * v ^ 2
  let β := a2 * v + 2 * a4 * v ^ 2
  let γ := a0 + a2 * v + a4 * v ^ 2
  have hv : v ^ p = v := by
    dsimp only [v]
    have h5p : (5 : K) ^ p = 5 := by
      simpa only [Nat.cast_ofNat] using
        (WPFiniteField.natCast_pow_char (K := K) p 5)
    rw [div_pow, one_pow, h5p]
  have hSp : (squaredCoordinate : K[X]) ^ p = C v * (X ^ p + 1) := by
    have hv' : ((5 : K)⁻¹) ^ p = (5 : K)⁻¹ := by
      simpa only [v, one_div] using hv
    simp only [squaredCoordinate, mul_pow, ← map_pow, hv', add_pow_char, one_pow]
    simp only [v, one_div]
  have hS2p : (squaredCoordinate : K[X]) ^ (2 * p) =
      (C v * (X ^ p + 1)) ^ 2 := by
    rw [show 2 * p = p * 2 by omega, pow_mul, hSp]
  have hX2p : (X : K[X]) ^ (2 * p) = (X ^ p) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hQ : Q = C α * X ^ (2 * p) + C β * X ^ p + C γ := by
    dsimp only [Q]
    rw [hSp, hS2p, hX2p]
    dsimp only [α, β, γ]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  refine ⟨α, β, γ, ?_⟩
  rw [hQ] at hG
  dsimp only [Gx] at hG
  linear_combination hG

private theorem eval_map_cast (p : ℕ) [Fact p.Prime] [CharP K p]
    (P : (ZMod p)[X]) (a : ZMod p) :
    (P.map (φ (K := K) p)).eval (φ (K := K) p a) = φ (K := K) p (P.eval a) := by
  rw [eval_map, eval₂_at_apply]

theorem actual_endpoint_data (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (fK (K := K) p hp).eval 4 = 1 ∧ (fK (K := K) p hp).eval (1 / 4) = 1 ∧
      (HK (K := K) p hp).eval 4 =
        -4 * (WPFiniteInversion.integerFermatQuotient p 2 : K) ∧
      (HK (K := K) p hp).eval (1 / 4) =
        (1 / 4 : K) * (WPFiniteInversion.integerFermatQuotient p 2 : K) := by
  have hf : halfPullbackField p hp =
      (WPActualNativeHasse.nativeField p (p / 6)).comp
        (WPHasseIntegralTransport.fieldV p) := by
    rw [halfPullbackField_eq,
      WPActualNativeHasse.actual_full_native_field_cutoff p ((p - 1) / 2)
        (by omega) (by omega) (by
          have := Nat.div_mul_le_self p 6
          have := half_exponent p hp
          omega)]
  have hf4 : (halfPullbackField p hp).eval 4 = 1 := by
    rw [hf]
    exact WPHasseIntegralTransport.actual_native_V_endpoint p
  have hfq : (halfPullbackField p hp).eval (1 / 4) = 1 := by
    rw [hf, one_div]
    exact WPActualHasseReciprocal.actual_native_V_inverse_endpoint p (by omega)
  have hχ := ActualChiEndpoints.actual_chi_field_endpoints p hp
  have hs4 := congrArg
    (LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
      (ActualChiEndpoints.fourUnit p hp)) (shiftedChiField_toLaurent p hp)
  have hsq := congrArg
    (LaurentPolynomial.eval₂ (RingHom.id (ZMod p))
      (ActualChiEndpoints.fourUnit p hp)⁻¹) (shiftedChiField_toLaurent p hp)
  have hv : (ActualChiEndpoints.fourUnit (K := ZMod p) p hp : ZMod p) = 4 := rfl
  simp only [map_mul, LaurentPolynomial.eval₂_T_n,
    LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
    Units.val_inv_eq_inv_val, hv, inv_pow, ZMod.pow_card,
    hχ.1, hχ.2] at hs4 hsq
  have hH4 : (shiftedChiField p hp).eval 4 =
      -4 * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
    linear_combination hs4
  have hHq : (shiftedChiField p hp).eval (1 / 4) =
      (1 / 4 : ZMod p) * (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
    simpa only [one_div] using hsq
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [fK, map_ofNat, hf4, map_one] using
      eval_map_cast (K := K) p (halfPullbackField p hp) 4
  · simpa only [fK, map_div₀, map_one, map_ofNat, hfq] using
      eval_map_cast (K := K) p (halfPullbackField p hp) (1 / 4)
  · simpa only [HK, map_ofNat, hH4, map_neg, map_mul, map_intCast] using
      eval_map_cast (K := K) p (shiftedChiField p hp) 4
  · simpa only [HK, map_div₀, map_one, map_ofNat, hHq,
      map_mul, map_intCast] using
      eval_map_cast (K := K) p (shiftedChiField p hp) (1 / 4)

/-- Actual three phases and exactly the two actual endpoint relations. -/
theorem actual_half_chi_three_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    ∃ α β γ : K,
      χK (K := K) p hp = (fK (K := K) p hp).toLaurent *
        (WPFiniteZSource.P p u +
          LaurentPolynomial.C α * T (p : ℤ) +
          LaurentPolynomial.C β +
          LaurentPolynomial.C γ * T (-(p : ℤ))) +
        ActualChiEndpoints.zeta p * (CBK (K := K) p).toLaurent ∧
      α / 4 + β + 4 * γ = 0 ∧
      4 * α + β + γ / 4 = 0 := by
  obtain ⟨α, β, γ, hpoly⟩ := actual_polynomial_three_phase (K := K) p hp u
  have he := congrArg (fun P : K[X] => P.toLaurent) hpoly
  simp only [map_mul, map_add, map_pow, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, LaurentPolynomial.T_pow, mul_one] at he
  rw [HK_toLaurent p hp, ← WPFiniteZSource.P_numerator p u] at he
  have ht : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  have ht2 : (T (-(p : ℤ)) * T ((2 * p : ℕ) : ℤ) : K[T;T⁻¹]) =
      T (p : ℤ) := by
    rw [← LaurentPolynomial.T_add]
    congr 1
    omega
  have hLaurent :
      χK (K := K) p hp = (fK (K := K) p hp).toLaurent *
        (WPFiniteZSource.P p u +
          LaurentPolynomial.C α * T (p : ℤ) +
          LaurentPolynomial.C β +
          LaurentPolynomial.C γ * T (-(p : ℤ))) +
        ActualChiEndpoints.zeta p * (CBK (K := K) p).toLaurent := by
    calc
      χK (K := K) p hp = T (-(p : ℤ)) * (T (p : ℤ) * χK (K := K) p hp) := by
        rw [← mul_assoc, ht, one_mul]
      _ = T (-(p : ℤ)) *
          ((fK (K := K) p hp).toLaurent *
            (T (p : ℤ) * WPFiniteZSource.P p u +
              LaurentPolynomial.C α * T ((2 * p : ℕ) : ℤ) +
              LaurentPolynomial.C β * T (p : ℤ) +
              LaurentPolynomial.C γ) +
            LaurentPolynomial.C (1 / 3 : K) *
              WPFiniteZSource.Abar.toLaurent ^ p * (CBK (K := K) p).toLaurent) := by
        rw [he]
      _ = _ := by
        unfold ActualChiEndpoints.zeta
        linear_combination
          ((fK (K := K) p hp).toLaurent * WPFiniteZSource.P p u +
            (fK (K := K) p hp).toLaurent * LaurentPolynomial.C β) * ht +
          (fK (K := K) p hp).toLaurent * LaurentPolynomial.C α * ht2
  obtain ⟨hf4, hfq, hH4, hHq⟩ := actual_endpoint_data (K := K) p hp
  have hP := ActualChiEndpoints.finite_Pnumerator_endpoints (K := K) p hp u
  have h4 : (4 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4 (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hqp : (1 / 4 : K) ^ p = 1 / 4 := by
    rw [div_pow, one_pow, h4p]
  have h42p : (4 : K) ^ (2 * p) = 16 := by
    rw [show 2 * p = p + p by omega, pow_add, h4p]
    norm_num
  have hq2p : (1 / 4 : K) ^ (2 * p) = (1 / 4 : K) ^ 2 := by
    rw [show 2 * p = p + p by omega, pow_add, hqp, pow_two]
  have hA4 : (WPFiniteZSource.Abar : K[X]).eval 4 = 0 := by
    simp [WPFiniteZSource.Abar]
  have hAq : (WPFiniteZSource.Abar : K[X]).eval (1 / 4) = 0 := by
    simp [WPFiniteZSource.Abar, one_div, mul_inv_cancel₀ h4]
  have e4 := congrArg (fun P : K[X] => P.eval 4) hpoly
  have eq := congrArg (fun P : K[X] => P.eval (1 / 4)) hpoly
  simp only [eval_mul, eval_add, eval_C, eval_pow, eval_X,
    hf4, hH4, hP.1, hA4, h4p, h42p,
    zero_pow (by omega : p ≠ 0), zero_mul, mul_zero, add_zero, one_mul] at e4
  simp only [eval_mul, eval_add, eval_C, eval_pow, eval_X,
    hfq, hHq, hP.2, hAq, hqp, hq2p,
    zero_pow (by omega : p ≠ 0), zero_mul, mul_zero, add_zero, one_mul] at eq
  have hpos : 16 * α + 4 * β + γ = 0 := by linear_combination -e4
  have hneg : α * (1 / 4 : K) ^ 2 + β * (1 / 4 : K) + γ = 0 := by
    linear_combination -eq
  refine ⟨α, β, γ, hLaurent, ?_, ?_⟩
  · field_simp [h4] at hneg ⊢
    linear_combination hneg
  · field_simp [h4]
    linear_combination hpos

end WPFieldAssembly.ActualThreePhase
