import WPFieldAssembly.NativeClosureMetricCarrier

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteWSource WPFiniteJHighCoefficient WPFiniteCubicLog
open WPFieldAssembly.NativeQuadraticInverse WPFieldAssembly.ConicKernel

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 2200000

/- STATEMENT_FIDELITY: For a natural prime p>=19, B is precisely
ActualFirstGreen.B=actualLegendreJacobi*properLegendreJacobi, CB is its
existing conic carrier, and N=(p-1)/2. Its actual odd reflection determines
the zero origin and even divX quotient. The same quadraticInverse then
reconstructs B and gives the full squaredCoordinate^(N+1) factor of CB,
with coefficient 1/25 and the original fieldV. No generated finite data,
endpoint value, signed-band extraction or residue evaluation is used.
The field interface uses the exact coefficient map of PB and fieldV, so
specializing its ring homomorphism to the existing ThreePhase map gives CBK.
This factor alone does not collect Wneed or evaluate the actual NC77 scalar. -/

/-- The actual odd B has its genuine zero origin. -/
theorem actual_B_origin (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ActualFirstGreen.B p).coeff 0 = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have he := congrArg (fun P : (ZMod p)[X] => P.coeff 0)
    (ActualFirstGreen.actual_B_odd p hp)
  simp only [WPFieldAssembly.ConicKernel.coeff_comp_neg, pow_zero,
    coeff_neg] at he
  have hz : (2 : ZMod p) * (ActualFirstGreen.B p).coeff 0 = 0 := by
    linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left h2

/-- Removing the original odd X factor gives the actual even quotient. -/
theorem actual_B_divX_even (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ActualFirstGreen.B p).divX.comp (-X) = (ActualFirstGreen.B p).divX := by
  have hd : X * (ActualFirstGreen.B p).divX = ActualFirstGreen.B p := by
    simpa only [actual_B_origin p hp, map_zero, add_zero] using
      X_mul_divX_add (ActualFirstGreen.B p)
  have hr := congrArg (fun P : (ZMod p)[X] => P.comp (-X)) hd
  simp only [mul_comp, X_comp, ActualFirstGreen.actual_B_odd p hp] at hr
  apply mul_left_cancel₀ (neg_ne_zero.mpr (X_ne_zero : (X : (ZMod p)[X]) ≠ 0))
  linear_combination hr + hd

/-- The whole B is reconstructed from its even quotient without a local inverse. -/
theorem actual_PB_B_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualFirstGreen.B p = X *
      (quadraticInverse (ActualFirstGreen.B p).divX).comp (1 - X ^ 2) := by
  let Q := (ActualFirstGreen.B p).divX
  have hQ : Q.comp (-X) = Q := actual_B_divX_even p hp
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hcontract : (contract 2 Q).comp (X ^ 2) = Q := by
    rw [← expand_eq_comp_X_pow]
    ext n
    rw [coeff_expand (by norm_num : 0 < 2)]
    by_cases hn : 2 ∣ n
    · rw [if_pos hn, coeff_contract (by norm_num : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hn]
    · rw [if_neg hn]
      have ho : Odd n := (Nat.even_or_odd n).resolve_left
        (by rintro ⟨a, ha⟩; exact hn ⟨a, by omega⟩)
      have he := congrArg (fun P : (ZMod p)[X] => P.coeff n) hQ
      rw [WPFieldAssembly.ConicKernel.coeff_comp_neg, ho.neg_pow, one_pow] at he
      have hz : (2 : ZMod p) * Q.coeff n = 0 := by linear_combination -he
      exact ((mul_eq_zero.mp hz).resolve_left h2).symm
  have hi : (quadraticInverse Q).comp (1 - X ^ 2) = Q := by
    rw [quadraticInverse, comp_assoc]
    simp only [sub_comp, one_comp, X_comp, sub_sub_cancel]
    exact hcontract
  rw [hi]
  symm
  simpa only [Q, actual_B_origin p hp, map_zero, add_zero] using
    X_mul_divX_add (ActualFirstGreen.B p)

/-- The original CB carrier has its full branch factor before taking any residue. -/
theorem actual_CB_PB_source (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    ActualFirstGreen.CB p = C (1 / 25 : ZMod p) *
      (squaredCoordinate : (ZMod p)[X]) ^ (((p - 1) / 2) + 1) *
      (4 * X - 11) * (quadraticInverse (ActualFirstGreen.B p).divX).comp
        (WPHasseIntegralTransport.fieldV p) := by
  have h5 : (5 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have h25 : (25 : ZMod p) ≠ 0 := by
    rw [show (25 : ZMod p) = 5 ^ 2 by norm_num]
    exact pow_ne_zero 2 h5
  have hc : (C (1 / 25 : ZMod p) : (ZMod p)[X]) * 5 = C (1 / 5 : ZMod p) := by
    change C (1 / 25 : ZMod p) * C 5 = C (1 / 5 : ZMod p)
    rw [← C_mul]
    congr 1
    apply (eq_div_iff h5).mpr
    (field_simp [h25]; ring)
  have hcd : (conic : (ZMod p)[X]).natDegree = 2 := by
    unfold conic
    compute_degree
    exact h5
  apply comp_injective_nonconstant
    (conic : (ZMod p)[X]) (by rw [hcd]; norm_num)
  dsimp only
  have hV : (WPHasseIntegralTransport.fieldV p).comp conic =
      1 - (Tc : (ZMod p)[X]) ^ 2 := WPActualNativeJacobiJet.actual_native_V_conic p hp
  have hl : (4 * X - 11 : (ZMod p)[X]).comp conic = 5 * (4 * X ^ 2 - 3) := by
    simp only [conic, sub_comp, mul_comp, ofNat_comp, X_comp]
    ring
  have hn : 2 * (((p - 1) / 2) + 1) = p + 1 := by
    have := half_exponent p hp
    omega
  have hs : ((squaredCoordinate : (ZMod p)[X]) ^ (((p - 1) / 2) + 1)).comp conic =
      X ^ (p + 1) := by
    rw [pow_comp, squaredCoordinate_conic p hp, ← pow_mul, hn]
  have hb := congrArg (fun P : (ZMod p)[X] => P.comp Tc)
    (actual_PB_B_source p hp)
  simp only [mul_comp, X_comp, comp_assoc, sub_comp, one_comp, pow_comp] at hb
  rw [(ActualFirstGreen.actual_carrier_pullbacks p hp).1, ActualFirstGreen.CBt, hb]
  rw [mul_comp, mul_comp, mul_comp, C_comp, hs, hl, comp_assoc, hV]
  rw [pow_succ (X : (ZMod p)[X]) p]
  have ht : (Tc : (ZMod p)[X]) = X * (4 * X ^ 2 - 3) := by
    unfold Tc
    ring
  linear_combination
    (C (1 / 5 : ZMod p) * X ^ p *
      (quadraticInverse (ActualFirstGreen.B p).divX).comp (1 - Tc ^ 2)) * ht -
    (X ^ p * X * (4 * X ^ 2 - 3)) *
      (quadraticInverse (ActualFirstGreen.B p).divX).comp (1 - Tc ^ 2) * hc

/-- The full CB branch source transports to the consumer's characteristic-p field. -/
theorem actual_CB_mapped_PB_source {K : Type*} [Field K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (f : ZMod p →+* K) :
    (ActualFirstGreen.CB p).map f = C (1 / 25 : K) *
      (squaredCoordinate : K[X]) ^ (((p - 1) / 2) + 1) * (4 * X - 11) *
      ((quadraticInverse (ActualFirstGreen.B p).divX).map f).comp
        ((WPHasseIntegralTransport.fieldV p).map f) := by
  have hs : (squaredCoordinate : (ZMod p)[X]).map f = (squaredCoordinate : K[X]) := by
    simp only [squaredCoordinate, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
      map_inv₀, map_ofNat]
  have he := congrArg (fun P : (ZMod p)[X] => P.map f) (actual_CB_PB_source p hp)
  simpa only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_comp, map_div₀, map_one, map_ofNat, hs] using he

end WPFieldAssembly.ActualBpairContraction
