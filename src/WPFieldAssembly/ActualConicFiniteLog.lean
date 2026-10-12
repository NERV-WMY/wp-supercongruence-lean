import WPFieldAssembly.ActualJointGreen
import WPFieldAssembly.ActualGreenPrimitive

open scoped Polynomial LaurentPolynomial
open Polynomial WPPIntegralReduction
open LaurentPolynomial (T)

namespace WPFieldAssembly.ActualJointGreen

variable (p : ℕ) [Fact p.Prime]

noncomputable def finiteEvenSquaredQ : ℚ[X] := contract 2 (finiteEvenLogQ p)

theorem finiteEvenSquaredIntegral_value (hp : 19 ≤ p) :
    (finiteEvenSquaredIntegral p).map (integralRationals p).subtype =
      finiteEvenSquaredQ p := by
  rw [finiteEvenSquaredIntegral, map_contract (by norm_num : (2 : ℕ) ≠ 0),
    finiteEvenLogIntegral_value p hp]
  rfl

omit [Fact p.Prime] in
private theorem finiteEvenLogQ_even :
    (finiteEvenLogQ p).comp (-X) = finiteEvenLogQ p := by
  simp only [finiteEvenLogQ, sub_comp, C_comp, comp_assoc,
    one_comp, pow_comp, X_comp, neg_sq]

omit [Fact p.Prime] in
theorem finiteEvenSquaredQ_pullback :
    (finiteEvenSquaredQ p).comp (X^2) = finiteEvenLogQ p := by
  have he := ActualGreenPrimitive.even_expand_contract
    (finiteEvenLogQ p) (by norm_num : (2 : ℚ) ≠ 0) (finiteEvenLogQ_even p)
  rw [expand_eq_comp_X_pow] at he
  exact he

noncomputable def finiteConicLogIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (finiteEvenSquaredIntegral p).comp
    (1 - WPHasseIntegralTransport.integralV p (by omega))

noncomputable def finiteConicLogQ : ℚ[X] :=
  (finiteEvenSquaredQ p).comp (1 - WPActualPullbackSource.Vpolynomial)

theorem finiteConicLogIntegral_value (hp : 19 ≤ p) :
    (finiteConicLogIntegral p hp).map (integralRationals p).subtype =
      finiteConicLogQ p := by
  simp only [finiteConicLogIntegral, Polynomial.map_comp, Polynomial.map_sub,
    Polynomial.map_one, finiteEvenSquaredIntegral_value p hp,
    WPHasseIntegralTransport.integralV_map_rational, finiteConicLogQ]

omit [Fact p.Prime] in
theorem finiteConicLogQ_actual_pullback (_hp : 19 ≤ p) :
    (finiteConicLogQ p).comp (ActualGreenPrimitive.greenConicQ p) =
      (finiteEvenLogQ p).comp (WPFiniteCubicLog.Tc : ℚ[X]) := by
  have hV : WPActualPullbackSource.Vpolynomial.comp
      (ActualGreenPrimitive.greenConicQ p) = 1 - (WPFiniteCubicLog.Tc : ℚ[X])^2 := by
    have h125 : (125 : ℚ[X]) * C (1 / 125 : ℚ) = 1 := by
      change C (125 : ℚ) * C (1 / 125 : ℚ) = C 1
      rw [← C_mul]
      norm_num
    simp only [WPActualPullbackSource.Vpolynomial,
      ActualGreenPrimitive.greenConicQ, mul_comp, C_comp, sub_comp,
      ofNat_comp, pow_comp, one_comp, X_comp, WPFiniteCubicLog.Tc]
    linear_combination (1 - (4 * X ^ 3 - 3 * X) ^ 2) * h125
  rw [finiteConicLogQ, comp_assoc, sub_comp, one_comp, hV, sub_sub_cancel]
  have he := congrArg (fun P : ℚ[X] => P.comp (WPFiniteCubicLog.Tc : ℚ[X]))
    (finiteEvenSquaredQ_pullback p)
  simpa only [comp_assoc, pow_comp, X_comp] using he

noncomputable def finiteLogCIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(((p-1)/2 : ℕ) : integralRationals p) *
    (finiteConicLogIntegral p hp).coeff ((p-1)/2)

theorem finiteLogCIntegral_value (hp : 19 ≤ p) :
    (finiteLogCIntegral p hp).val = -(((p-1)/2 : ℕ) : ℚ) *
      (finiteConicLogQ p).coeff ((p-1)/2) := by
  change -(((p-1)/2 : ℕ) : ℚ) *
    (integralRationals p).subtype ((finiteConicLogIntegral p hp).coeff ((p-1)/2)) = _
  rw [← coeff_map, finiteConicLogIntegral_value p hp]

theorem actual_finite_log_C_residue (hp : 19 ≤ p) :
    resInfinity (T (-(((p-1)/2 : ℕ) : ℤ)) *
      WPFiniteLaurentDifferential.D (finiteConicLogQ p).toLaurent) =
        (finiteLogCIntegral p hp).val := by
  rw [shifted_derivative_resInfinity, finiteLogCIntegral_value p hp]

theorem finiteEvenSquaredQ_source (hp : 19 ≤ p) :
    2 * (1-X) * (finiteEvenSquaredQ p).derivative =
      1-X^((p-1)/2) := by
  let E : ℚ[X] := 2*(1-X)*(finiteEvenSquaredQ p).derivative -
    (1-X^((p-1)/2))
  have hd := congrArg Polynomial.derivative (finiteEvenSquaredQ_pullback p)
  simp only [derivative_comp, derivative_X_pow, map_ofNat, Nat.cast_ofNat] at hd
  have hs := finiteEvenLogQ_source p hp
  have hn : p = 2*((p-1)/2)+1 := WPFiniteWSource.half_exponent p hp
  have hpow : (X : ℚ[X])^p = X*(X^2)^((p-1)/2) := by
    conv_lhs => rw [hn, pow_succ, pow_mul]
    ring
  rw [hpow] at hs
  have hm : X * E.comp (X^2) = 0 := by
    simp only [E, sub_comp, mul_comp, ofNat_comp, one_comp,
      X_comp, pow_comp]
    linear_combination (1-X^2)*hd + hs
  have hc : E.comp (X^2) = 0 := (mul_eq_zero.mp hm).resolve_left X_ne_zero
  have he : E = 0 := ConicKernel.comp_injective_nonconstant
    (X^2)
    (by rw [natDegree_X_pow]; norm_num) (by simpa only [zero_comp] using hc)
  dsimp only [E] at he
  exact sub_eq_zero.mp he

theorem actual_finite_conic_log_source (hp : 19 ≤ p) :
    2 * WPActualPullbackSource.Vpolynomial * (finiteConicLogQ p).derivative =
      ((1-WPActualPullbackSource.Vpolynomial)^((p-1)/2)-1) *
        WPActualPullbackSource.Vpolynomial.derivative := by
  have he := congrArg (fun P : ℚ[X] =>
    P.comp (1-WPActualPullbackSource.Vpolynomial)) (finiteEvenSquaredQ_source p hp)
  simp only [mul_comp, ofNat_comp, sub_comp, one_comp, X_comp,
    pow_comp, sub_sub_cancel] at he
  rw [finiteConicLogQ, derivative_comp, derivative_sub, derivative_one, zero_sub]
  linear_combination -WPActualPullbackSource.Vpolynomial.derivative * he

theorem actual_finite_conic_log_Abar_source (hp : 19 ≤ p) :
    2 * (WPFiniteZSource.Abar : ℚ[X]) * (finiteConicLogQ p).derivative -
      3*(4*X-11) =
        -C (3*(1/5 : ℚ)^(p-1)) *
          (ActualGreenPrimitive.greenCoordinateQ p)^((p-1)/2) * (4*X-11)^p := by
  let V := WPActualPullbackSource.Vpolynomial
  let s := ActualGreenPrimitive.greenCoordinateQ p
  let c : ℚ[X] := 4*X-11
  let A : ℚ[X] := WPFiniteZSource.Abar
  have hv : 1-V = C (1/25 : ℚ)*s*c^2 := by
    have ht : (125 : ℚ[X])-(4*X-1)^2*(4-X)=
        (X+1)*(4*X-11)^2 := by ring
    have hc : C (1/125 : ℚ)*125=(1 : ℚ[X]) := by
      change C (1/125 : ℚ)*C 125=C 1
      rw [←C_mul]
      norm_num
    calc
      _ = C (1/125 : ℚ)*(125-(4*X-1)^2*(4-X)) := by
        rw [mul_sub,hc]
        simp only [V,WPActualPullbackSource.Vpolynomial]
        ring
      _ = C (1/125 : ℚ)*((X+1)*(4*X-11)^2) := by rw [ht]
      _ = _ := by
        have hscale : (C (1/125 : ℚ) : ℚ[X]) = C (1/25 : ℚ) * C (1/5 : ℚ) := by
          rw [← C_mul]
          norm_num
        simp only [s,c,ActualGreenPrimitive.greenCoordinateQ]
        rw [hscale]
        ring
  have hd : A*V.derivative = -3*c*V := by
    have ht : (4-X : ℚ[X])*(4*X-1)*
        (((4*X-1)^2*(4-X)) : ℚ[X]).derivative=
        -3*(4*X-11)*((4*X-1)^2*(4-X)) := by
      norm_num [derivative_mul,derivative_pow_succ,derivative_X,
        derivative_sub,derivative_ofNat,derivative_one,zero_sub,C_ofNat]
      ring
    simp only [A,V,c,WPFiniteZSource.Abar,WPActualPullbackSource.Vpolynomial,
      mul_assoc,derivative_C_mul]
    linear_combination C (1/125 : ℚ)*ht
  have hn : 2*((p-1)/2)+1 = p := by
    have hh := WPFiniteWSource.half_exponent p hp
    omega
  have hk : (C (1/25 : ℚ)*s*c^2)^((p-1)/2)*c =
      C ((1/5 : ℚ)^(p-1))*s^((p-1)/2)*c^p := by
    rw [mul_pow, mul_pow, ← C_pow, ←pow_mul]
    have hnum : (1/25 : ℚ)^((p-1)/2) = (1/5 : ℚ)^(p-1) := by
      rw [show (1/25 : ℚ) = (1/5)^2 by norm_num, ← pow_mul]
      congr 1
      omega
    rw [hnum]
    have hpow : c^(2*((p-1)/2))*c = c^p := by rw [← pow_succ, hn]
    linear_combination C ((1/5 : ℚ)^(p-1))*s^((p-1)/2)*hpow
  have hkv : (1-V)^((p-1)/2)*c =
      C ((1/5 : ℚ)^(p-1))*s^((p-1)/2)*c^p := by
    simpa only [hv] using hk
  have he := actual_finite_conic_log_source p hp
  change 2*V*(finiteConicLogQ p).derivative =
    ((1-V)^((p-1)/2)-1)*V.derivative at he
  have he2 : V*(2*A*(finiteConicLogQ p).derivative-3*c +
      C (3*(1/5 : ℚ)^(p-1))*s^((p-1)/2)*c^p) = 0 := by
    rw [map_mul,map_ofNat]
    linear_combination A*he + ((1-V)^((p-1)/2)-1)*hd - 3*V*hkv
  have hV0 : V ≠ 0 := by
    intro hz
    have h := congrArg (fun P : ℚ[X] => P.eval 0) hz
    norm_num [V, WPActualPullbackSource.Vpolynomial] at h
  have hz := (mul_eq_zero.mp he2).resolve_left hV0
  change 2*A*(finiteConicLogQ p).derivative-3*c =
    -C (3*(1/5 : ℚ)^(p-1))*s^((p-1)/2)*c^p
  linear_combination hz

end WPFieldAssembly.ActualJointGreen
