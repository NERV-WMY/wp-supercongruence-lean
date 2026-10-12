import WPFieldAssembly.ActualTC1Family

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualRankTwoParameter
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoFirstLift
  WPActualRankTwoFixedDegree WPActualRankTwoLowTaylor WPActualRankTwoHatLift
  WPActualRankTwoFiniteLegendre WPFieldAssembly.ActualBalancedCarry
  WPFieldAssembly.ActualTC1Family WPFieldAssembly.ActualNextHermite
  WPFieldAssembly.ActualDeltaUNextSource WPFieldAssembly.ResidualProjection
  WPFieldAssembly.NativeQuadraticInverse WPActualRankTwoComparison
  WPActualRankTwoProper WPActualCMGauss WPActualGaussBottom
  WPNativeParameterTaylor WPActualRankTwoResidueSource

namespace WPFieldAssembly.ActualBalancedNodeAttachment
set_option maxHeartbeats 1600000

section GenericEvaluation
variable {K : Type*} [CommRing K]

private theorem polynomial_natCast (n : ℕ) : (n : K[X]) = C (n : K) :=
  (_root_.map_natCast (C : K →+* K[X]) n).symm

theorem DT_eval_C (P : EtaPoly K) (t : K) :
    (DT P).eval (C t) = (P.eval (C t)).derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [_root_.map_add, eval_add, ihP, ihQ]
  | monomial n P =>
      have hd : DT (monomial n P) = monomial n P.derivative := by
        apply Polynomial.ext
        intro j
        simp only [DT_coeff, coeff_monomial]
        split_ifs <;> simp
      rw [hd]
      simp [eval_monomial, derivative_mul, derivative_pow]

theorem eval_C_endLift (P : EtaPoly K) (t : K) :
    ((endLift P).eval (C t)).eval 1 = (P.eval (C t)).eval 1 := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ => simp only [_root_.map_add, eval_add, ihP, ihQ]
  | monomial n P => simp [endLift, eval_monomial]

theorem eval_C_degree (P : EtaPoly K) (t : K) :
    (P.eval (C t)).natDegree ≤ (Bivariate.swap P).natDegree := by
  have he : (Bivariate.swap P).map (evalRingHom t) = P.eval (C t) := by
    have hc : (evalRingHom t).comp (C : K →+* K[X]) = RingHom.id K := by
      ext z
      simp
    induction P using Polynomial.induction_on' with
    | add P Q ihP ihQ => simp only [_root_.map_add, Polynomial.map_add, eval_add, ihP, ihQ]
    | monomial n P =>
        rw [Bivariate.swap_monomial]
        simp [Polynomial.map_map, eval_monomial, hc]
  rw [← he]
  exact natDegree_map_le

noncomputable def parameterA (m : ℕ) (t : K) (P : K[X]) : K[X] :=
  legendreJacobi m P + C t * (X * P.derivative - C (m : K) * P)

theorem scaledEta_eval_equation [IsDomain K] (u : ℕ → K) (m : ℕ)
    (hu : UnitsTo u m) (t : K) :
    parameterA m t ((scaledEta u m).eval (C t)) = 0 := by
  have he := congrArg (fun P : EtaPoly K => P.eval (C t))
    (scaledEta_equation u m hu)
  simp only [etaAOperator, tq, tx, ActualTC1Family.eta, eval_sub, eval_add, eval_mul,
    eval_pow, eval_one, eval_C, eval_X, eval_natCast, eval_ofNat, eval_zero, DT_eval_C] at he
  dsimp only [parameterA, legendreJacobi]
  simp only [_root_.map_add, _root_.map_mul, _root_.map_one, _root_.map_natCast] at he ⊢
  linear_combination he
end GenericEvaluation

variable (p : ℕ) [Fact p.Prime]

noncomputable def etaStar (hp : 19 ≤ p) : integralRationals p :=
  (p : integralRationals p) * (2 * integralSixth p (by omega))
theorem etaStar_value (hp : 19 ≤ p) : (etaStar p hp).val = (p : ℚ) / 3 := by
  change (p : ℚ) * (2 * (1 / 6 : ℚ)) = _; ring
theorem etaStar_field (hp : 19 ≤ p) : residueHom p (etaStar p hp) = 0 := by
  simp only [etaStar, _root_.map_mul, _root_.map_natCast, ZMod.natCast_self, zero_mul]

noncomputable def metricStar (hp : 19 ≤ p) : integralRationals p :=
  ∏ j ∈ Finset.range (p / 6),
    (1 - smallIntegralInverse p (j + 1) * etaStar p hp)

theorem metricStar_field (hp : 19 ≤ p) : residueHom p (metricStar p hp) = 1 := by
  simp only [metricStar, map_prod, _root_.map_sub, _root_.map_one, _root_.map_mul,
    etaStar_field, mul_zero, sub_zero, Finset.prod_const_one]

theorem metricStar_unit (hp : 19 ≤ p) :
    (metricStar p hp).val ≠ 0 ∧ (metricStar p hp).val⁻¹ ∈ integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [metricStar_field]
  exact one_ne_zero

noncomputable def metricStarInverse (hp : 19 ≤ p) : integralRationals p :=
  ⟨(metricStar p hp).val⁻¹, (metricStar_unit p hp).2⟩
theorem metricStar_mul_inverse (hp : 19 ≤ p) :
    metricStar p hp * metricStarInverse p hp = 1 := by
  apply Subtype.ext
  exact mul_inv_cancel₀ (metricStar_unit p hp).1
theorem metricStarInverse_field (hp : 19 ≤ p) :
    residueHom p (metricStarInverse p hp) = 1 := by
  have he := congrArg (residueHom p) (metricStar_mul_inverse p hp)
  simpa only [_root_.map_mul, _root_.map_one, metricStar_field, one_mul] using he

noncomputable def scaledStar (hp : 19 ≤ p) : (integralRationals p)[X] :=
  (scaledEta (fun j => smallIntegralInverse p j) (p / 6)).eval (C (etaStar p hp))
noncomputable def balancedFirstIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (metricStarInverse p hp) * scaledStar p hp

private theorem metricFactor_eval (m : ℕ) (hp : 19 ≤ p) :
    (metricFactor (fun j => smallIntegralInverse p j) m).eval (C (etaStar p hp)) =
      C (∏ j ∈ Finset.range m, (1 - smallIntegralInverse p (j + 1) * etaStar p hp)) := by
  induction m with
  | zero => simp [metricFactor]
  | succ m ih =>
      simp only [metricFactor, eval_mul, eval_sub, eval_one, eval_C, eval_X,
        cc, ActualTC1Family.eta, ih, Finset.prod_range_succ,
        _root_.map_mul, _root_.map_sub, _root_.map_one]

private theorem scaledStar_endpoint (hp : 19 ≤ p) :
    (scaledStar p hp).eval 1 = metricStar p hp := by
  have he := congrArg (fun P : EtaPoly (integralRationals p) =>
    (P.eval (C (etaStar p hp))).eval 1)
    (scaledEta_endpoint (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ (by omega)))
  rw [eval_C_endLift, metricFactor_eval, eval_C] at he
  exact he

theorem balancedFirstIntegral_endpoint (hp : 19 ≤ p) :
    (balancedFirstIntegral p hp).eval 1 = 1 := by
  rw [balancedFirstIntegral, eval_mul, eval_C, scaledStar_endpoint, mul_comm,
    metricStar_mul_inverse]

theorem balancedFirstIntegral_degree (hp : 19 ≤ p) :
    (balancedFirstIntegral p hp).natDegree ≤ p / 6 := by
  apply (natDegree_C_mul_le _ _).trans
  exact (eval_C_degree _ _).trans (scaledEta_T_degree _ _)

theorem balancedFirstIntegral_equation (hp : 19 ≤ p) :
    parameterA (p / 6) (etaStar p hp) (balancedFirstIntegral p hp) = 0 := by
  have he := scaledEta_eval_equation (fun j => smallIntegralInverse p j) (p / 6)
    (integral_units p _ (by omega)) (etaStar p hp)
  change parameterA (p / 6) (etaStar p hp) (scaledStar p hp) = 0 at he
  unfold parameterA at he
  unfold parameterA balancedFirstIntegral
  rw [legendreJacobi_C_mul]
  simp only [derivative_C_mul]
  linear_combination C (metricStarInverse p hp) * he

theorem parameterA_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (m : ℕ) (t : K) (P : K[X]) :
    (parameterA m t P).map f = parameterA m (f t) (P.map f) := by
  simp only [parameterA, legendreJacobi_map, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.derivative_map, Polynomial.map_natCast, _root_.map_natCast]

private theorem actual_gauss_pivot_ne_zero (hp : 19 ≤ p) (n : ℕ) :
    ((n : ℚ) + 1 - (p : ℚ) / 6) ≠ 0 := by
  intro hz
  have hq : (p : ℚ) = 6 * ((n + 1 : ℕ) : ℚ) := by
    push_cast
    linear_combination -6 * hz
  have hn : p = 6 * (n + 1) := by exact_mod_cast hq
  have h3 : 3 ∣ p := ⟨2 * (n + 1), by omega⟩
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h | h <;> omega

private theorem actual_gauss_kernel_zero (hp : 19 ≤ p) (P : ℚ[X])
    (h0 : P.eval 0 = 0) (hs : rankRegular (-(p : ℚ) / 6) P = 0) : P = 0 := by
  have he : rankEuler (-(p : ℚ) / 6) P = 0 := by
    rw [rankEuler_eq_X_regular, hs, mul_zero]
  have hc : ∀ n, P.coeff n = 0 := by
    intro n
    induction n with
    | zero => simpa only [coeff_zero_eq_eval_zero] using h0
    | succ n ih =>
        have h := congrArg (fun Q : ℚ[X] => Q.coeff (n + 1)) he
        rw [rankEuler_coeff_succ, coeff_zero, ih, mul_zero, sub_zero] at h
        have hu : 36 * ((n : ℚ) + 1) * ((n : ℚ) + 1 - (p : ℚ) / 6) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) (by positivity))
            (actual_gauss_pivot_ne_zero p hp n)
        exact (mul_eq_zero.mp (by simpa only [sub_eq_add_neg, neg_div] using h)).resolve_left hu
  ext n; simpa only [coeff_zero] using hc n

private theorem actual_jacobi_kernel_zero (hp : 19 ≤ p) (P : ℚ[X])
    (h1 : P.eval 1 = 0) (hs : rankJacobiClear (-(p : ℚ) / 6) P = 0) : P = 0 := by
  let q : ℚ[X] := C (1 / 2) * (1 - X)
  let g : ℚ[X] := 1 - 2 * X
  have hi := jacobi_coordinate_inverse (1 / 2 : ℚ) (by norm_num)
  have hqg : q.comp g = X := hi.1
  have hgq : g.comp q = X := hi.2
  have he := rankRegular_jacobi_comp (-(p : ℚ) / 6) (P.comp g)
  change (rankRegular (-(p : ℚ) / 6) (P.comp g)).comp q =
    rankJacobiClear (-(p : ℚ) / 6) ((P.comp g).comp q) at he
  rw [comp_assoc, hgq, comp_X, hs] at he
  have hr := congrArg (fun Q : ℚ[X] => Q.comp g) he
  rw [comp_assoc, hqg, comp_X, zero_comp] at hr
  have hz := actual_gauss_kernel_zero p hp (P.comp g)
    (by simp [eval_comp, g, h1]) hr
  have hh := congrArg (fun Q : ℚ[X] => Q.comp q) hz
  simpa only [comp_assoc, hgq, comp_X, zero_comp] using hh

theorem balancedFirstIntegral_value (hp : 19 ≤ p) :
    (balancedFirstIntegral p hp).map (integralRationals p).subtype = rankJacobiNode p 1 := by
  let P := (balancedFirstIntegral p hp).map (integralRationals p).subtype
  have hs : parameterA (p / 6) ((p : ℚ) / 3) P = 0 := by
    have he := congrArg (fun Q : (integralRationals p)[X] =>
      Q.map (integralRationals p).subtype) (balancedFirstIntegral_equation p hp)
    simp only [parameterA_map, Polynomial.map_zero] at he
    change parameterA (p / 6) (etaStar p hp).val P = 0 at he
    rw [etaStar_value] at he
    exact he
  have h1 : P.eval 1 = 1 := by
    have he := congrArg (integralRationals p).subtype (balancedFirstIntegral_endpoint p hp)
    simpa only [← eval_map_apply, _root_.map_one] using he
  have hP : rankJacobiClear (-(p : ℚ) / 6) P = 0 := by
    rw [actual_low_rankJacobi_operator p (by omega : 7 ≤ p)]
    have hm : C (12 * (p : ℚ)) = 36 * C ((p : ℚ) / 3) := by
      rw [show (36 : ℚ[X]) = C (36 : ℚ) by rfl, ← C_mul]
      congr 1; ring
    rw [hm]
    unfold parameterA at hs
    linear_combination 36 * hs
  have hnode : rankJacobiClear (-(p : ℚ) / 6) (rankJacobiNode p 1) = 0 := by
    simpa only [Nat.cast_one, neg_one_mul] using
      actual_rankJacobi_ODE p 1 (by omega : 7 ≤ p) (Or.inl rfl)
  have hz := actual_jacobi_kernel_zero p hp (P - rankJacobiNode p 1)
    (by rw [eval_sub, h1, rankJacobiNode_endpoint_one]; ring)
    (by rw [rankJacobiClear_sub, hP, hnode, sub_self])
  exact sub_eq_zero.mp hz

theorem balancedFirstIntegral_eq_rankIntegral (hp : 19 ≤ p) :
    balancedFirstIntegral p hp = rankIntegralJacobi p (by omega) 1 := by
  apply polynomial_subtype_injective p
  change (balancedFirstIntegral p hp).map (integralRationals p).subtype =
    (rankIntegralJacobi p (by omega : 7 ≤ p) 1).map (integralRationals p).subtype
  rw [balancedFirstIntegral_value p hp, rankIntegralJacobi_value]

theorem balancedFirstIntegral_field (hp : 19 ≤ p) :
    (balancedFirstIntegral p hp).map (residueHom p) = actualLegendreJacobi p := by
  rw [balancedFirstIntegral_eq_rankIntegral p hp, rankIntegralJacobi_field]

theorem balancedProper_literal (hp : 19 ≤ p) :
    balancedProperIntegral p hp =
      (properEta (fun j => smallIntegralInverse p j) (p / 6)).eval (C (etaStar p hp)) := by
  rw [balancedProperIntegral, properEtaIntegral_generic]
  rfl

theorem balancedProper_degree (hp : 19 ≤ p) :
    (balancedProperIntegral p hp).natDegree ≤ p / 6 - 1 := by
  rw [balancedProper_literal p hp]
  exact (eval_C_degree _ _).trans (properEta_T_degree _ _)

private theorem scaledStar_eq_metric_mul_balanced (hp : 19 ≤ p) :
    scaledStar p hp = C (metricStar p hp) * balancedFirstIntegral p hp := by
  rw [balancedFirstIntegral, ← mul_assoc, ← C_mul, metricStar_mul_inverse, C_1, one_mul]

theorem actual_evaluated_normalized_metric (hp : 19 ≤ p) :
    (1 - X ^ 2) *
      (balancedFirstIntegral p hp * (balancedProperIntegral p hp).derivative -
       (balancedFirstIntegral p hp).derivative * balancedProperIntegral p hp) -
      C (etaStar p hp) * X * balancedFirstIntegral p hp * balancedProperIntegral p hp =
      1 - C (metricStar p hp) * balancedFirstIntegral p hp ^ 2 := by
  have he := congrArg (fun P : EtaPoly (integralRationals p) =>
    P.eval (C (etaStar p hp)))
    (eta_metric (fun j => smallIntegralInverse p j) (p / 6) (integral_units p _ (by omega)))
  simp only [tq, tx, ActualTC1Family.eta, eval_mul, eval_sub, eval_pow, eval_one,
    eval_C, eval_X, DT_eval_C, metricFactor_eval] at he
  rw [← balancedProper_literal p hp] at he
  change (1 - X ^ 2) *
    (scaledStar p hp * (balancedProperIntegral p hp).derivative -
     (scaledStar p hp).derivative * balancedProperIntegral p hp) -
    C (etaStar p hp) * X * scaledStar p hp * balancedProperIntegral p hp =
      C (metricStar p hp) - scaledStar p hp ^ 2 at he
  rw [scaledStar_eq_metric_mul_balanced p hp, derivative_C_mul] at he
  have hg : C (metricStar p hp) ≠ (0 : (integralRationals p)[X]) := by
    apply C_ne_zero.mpr
    intro hz
    exact (metricStar_unit p hp).1 (congrArg Subtype.val hz)
  apply mul_left_cancel₀ hg
  linear_combination he

open WPFiniteCarry WPActualRankTwoCarryField

noncomputable def firstIncrement (hp : 19 ≤ p) : (integralRationals p)[X] :=
  lowCarryIntegral p (by omega)
noncomputable def properIncrement (hp : 19 ≤ p) : (integralRationals p)[X] :=
  C (2 * integralSixth p (by omega)) * ActualBalancedCarry.properEtaJet p +
    C (p : integralRationals p) * balancedProperRemainder p hp
noncomputable def centralLogT : (integralRationals p)[X] :=
  (integralCentralLog p).comp (1 - X ^ 2)
noncomputable def centralHatIntegral (hp : 19 ≤ p) : (integralRationals p)[X] :=
  integralLegendre p (p / 6) (by omega) *
    (centralLogT p - C (integralHarmonic p (p / 6))) -
    X ^ p * integralProperJacobi p (by omega)

theorem actual_first_increment_source (hp : 19 ≤ p) :
    balancedFirstIntegral p hp = integralLegendre p (p / 6) (by omega) +
      C (p : integralRationals p) * firstIncrement p hp := by
  apply polynomial_subtype_injective p
  simp only [balancedFirstIntegral_value, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_natCast, _root_.map_natCast,
    integralLegendre_value, firstIncrement, lowCarryIntegral_value]
  rw [polynomial_natCast (K := ℚ) p]
  linear_combination actual_lowCarryPolynomial_source p (by omega : 7 ≤ p)

theorem actual_evaluated_first_second_taylor (hp : 19 ≤ p) :
    balancedFirstIntegral p hp = integralLegendre p (p / 6) (by omega) -
      C (p : integralRationals p) * C (integralSixth p (by omega)) *
        fixedIntegralJetJacobi p (by omega) +
      C ((p : integralRationals p) ^ 2) * fixedIntegralErrorJacobi p (by omega) := by
  apply polynomial_subtype_injective p
  have hsix : (integralRationals p).subtype (integralSixth p (by omega)) =
      (1 / 6 : ℚ) := rfl
  simp only [balancedFirstIntegral_value, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_natCast,
    _root_.map_pow, _root_.map_natCast,
    integralLegendre_value, fixedIntegralJetJacobi_value,
    fixedIntegralErrorJacobi_value, hsix]
  simp only [polynomial_natCast (K := ℚ) p]
  change rankJacobiNode p 1 = rationalLegendre (p / 6) -
    C (p : ℚ) * C (1 / 6 : ℚ) * fixedJetJacobi (p / 6) +
    C (p : ℚ) ^ 2 * fixedErrorJacobi p
  have hc : C ((p : ℚ) / 6) = C (p : ℚ) * C (1 / 6 : ℚ) := by
    rw [← C_mul]; congr 1; ring
  have ht := actual_low_fixedTaylor_jacobi p (by omega : 7 ≤ p)
  rw [hc] at ht
  simp only [_root_.map_pow] at ht
  linear_combination ht

theorem actual_proper_increment_source (hp : 19 ≤ p) :
    balancedProperIntegral p hp = integralProperJacobi p (by omega) +
      C (p : integralRationals p) * properIncrement p hp := by
  have ht := actual_balanced_proper_taylor p hp
  rw [actual_proper_origin_integral p hp] at ht
  unfold properIncrement
  simp only [_root_.map_pow] at ht ⊢
  linear_combination ht

theorem firstIncrement_field (hp : 19 ≤ p) :
    (firstIncrement p hp).map (residueHom p) =
      -C (1 / 6 : ZMod p) * actualVariationField p (by omega) := by
  have h := actual_lowCarry_variation_field p (by omega : 7 ≤ p)
  change (firstIncrement p hp).map (residueHom p) +
    C (1 / 6 : ZMod p) * actualVariationField p (by omega) = 0 at h
  linear_combination h

theorem properIncrement_field (hp : 19 ≤ p) :
    (properIncrement p hp).map (residueHom p) = C (1 / 3 : ZMod p) * actualN1 p := by
  have h3 : (3 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 := WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have hc : (2 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p) := by
    change C (2 : ZMod p) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p)
    rw [← C_mul]
    congr 1
    field_simp [h3, h6]
    ring
  simp only [properIncrement, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_ofNat, Polynomial.map_natCast, _root_.map_natCast,
    _root_.map_mul, _root_.map_ofNat, integralSixth_field,
    actualN1]
  simp only [polynomial_natCast (K := ZMod p) p, ZMod.natCast_self,
    C_0, zero_mul, add_zero]
  rw [hc]



theorem centralHatIntegral_value (hp : 19 ≤ p) :
    (centralHatIntegral p hp).map (integralRationals p).subtype = centralRankHat p := by
  simp only [centralHatIntegral, centralLogT, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, Polynomial.map_comp, Polynomial.map_one,
    integralLegendre_value, integralProperJacobi_value,
    integralCentralLog_value p hp, integralHarmonic_value p (p / 6) (by omega)]
  rfl

theorem centralHatIntegral_field (hp : 19 ≤ p) :
    (centralHatIntegral p hp).map (residueHom p) = actualRankDividedField p (by omega) := by
  have hi : integralRankHat p (by omega : 7 ≤ p) = centralHatIntegral p hp +
      C (p : integralRationals p) *
        (integralLegendre p (p / 6) (by omega) *
          (C (integralEvenLogEndpointCarry p hp) - (integralSecondLog p).comp (1 - X ^ 2))) +
      C ((p : integralRationals p) ^ 2) *
        (integralLegendre p (p / 6) (by omega) * (integralLogRemainder p).comp (1 - X ^ 2)) := by
    apply polynomial_subtype_injective p
    have hcarry : (integralRationals p).subtype (integralEvenLogEndpointCarry p hp) =
        WPFiniteCarry.actualEvenLogEndpointCarry p := rfl
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_comp, Polynomial.map_one, Polynomial.map_natCast, _root_.map_pow, _root_.map_natCast,
      integralRankHat_value, centralHatIntegral_value p hp, integralLegendre_value,
      integralSecondLog_value p hp, hcarry]
    simpa only [polynomial_natCast (K := ℚ) p, _root_.map_pow] using
      actual_central_rank_hat_source p hp
  have hr := congrArg (fun P : (integralRationals p)[X] => P.map (residueHom p)) hi
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_natCast, _root_.map_pow, _root_.map_natCast,
    integralRankHat_field] at hr
  simp only [polynomial_natCast (K := ZMod p) p, ZMod.natCast_self,
    C_0, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul, add_zero] at hr
  rw [← actual_rankDividedField_eq_hat p hp] at hr
  exact hr.symm

/-- The exact evaluated proper polynomial; eta=p/3 remains literal. -/
noncomputable def balancedProperQ (hp : 19 ≤ p) : ℚ[X] :=
  (balancedProperIntegral p hp).map (integralRationals p).subtype

noncomputable def balancedGreenJ (hp : 19 ≤ p) : ℚ[X] :=
  2 * rankJacobiNode p 1 ^ 2 *
    ((rationalCentralLog p).comp (1 - X ^ 2) + C ((balancedProperQ p hp).eval 1)) -
  2 * X ^ p * rankJacobiNode p 1 * balancedProperQ p hp

noncomputable def balancedGreenNumerator (hp : 19 ≤ p) : ℚ :=
  -QO p (balancedGreenJ p hp) / 6 - QH p (rankJacobiNode p 1 ^ 2) / 2 -
    WPFirstResidue.LiteralNormalization.literalR0 p

theorem balancedGreenJ_endpoint (hp : 19 ≤ p) : (balancedGreenJ p hp).eval 1 = 0 := by
  simp only [balancedGreenJ, eval_sub, eval_add, eval_mul, eval_pow, eval_ofNat,
    eval_C, eval_X, one_pow, rankJacobiNode_endpoint_one,
    eval_comp, eval_sub, eval_one, sub_self, rationalCentralLog_origin]
  ring

private noncomputable def greenFunctional (Y n L : ℚ[X]) (r : ℚ) : ℚ :=
  -QO p (Y ^ 2 * L - X ^ p * Y * n) / 3 - QH p (Y ^ 2) / 2 - r

omit [Fact p.Prime] in
private theorem greenFunctional_taylor (Y n L a b : ℚ[X]) (r : ℚ) :
    greenFunctional p (Y + C (p : ℚ) * a) (n + C (p : ℚ) * b) L r =
      greenFunctional p Y n L r +
      (p : ℚ) *
        (-QO p (2 * Y * a * L - X ^ p * (a * n + Y * b)) / 3 - QH p (Y * a)) +
      (p : ℚ) ^ 2 *
        (-QO p (a ^ 2 * L - X ^ p * a * b) / 3 - QH p (a ^ 2) / 2) := by
  have hm : (Y + C (p : ℚ) * a) ^ 2 * L -
      X ^ p * (Y + C (p : ℚ) * a) * (n + C (p : ℚ) * b) =
      (Y ^ 2 * L - X ^ p * Y * n) +
      C (p : ℚ) * (2 * Y * a * L - X ^ p * (a * n + Y * b)) +
      C ((p : ℚ) ^ 2) * (a ^ 2 * L - X ^ p * a * b) := by
    simp only [_root_.map_pow]; ring
  have hs : (Y + C (p : ℚ) * a) ^ 2 =
      Y ^ 2 + C (p : ℚ) * (2 * (Y * a)) + C ((p : ℚ) ^ 2) * a ^ 2 := by
    simp only [_root_.map_pow]; ring
  unfold greenFunctional
  rw [hm, hs]
  simp only [QO_add, QO_C_mul, QH_add, QH_C_mul]
  rw [show (2 : ℚ[X]) = C (2 : ℚ) by rfl, QH_C_mul]
  ring

private theorem low_square_QO_zero (hp : 19 ≤ p) (P : ℚ[X])
    (hP : P.natDegree ≤ p / 6) : QO p (P ^ 2) = 0 := by
  unfold QO
  exact low_correction_both_projections_zero p hp _
    (NativeOriginalResidues.quadraticInverse_degree_of_le _ (p / 6) (natDegree_pow_le_of_le 2 hP)) 0

private theorem centralGreenNumerator_eq_functional (hp : 19 ≤ p) :
    centralGreenNumerator p = greenFunctional p
      (rationalLegendre (p / 6)) (rationalProperJacobi (p / 6))
      ((rationalCentralLog p).comp (1 - X ^ 2))
      (WPFirstResidue.LiteralNormalization.literalR0 p) := by
  have hc : rationalLegendre (p / 6) * centralRankHat p =
      (rationalLegendre (p / 6) ^ 2 * (rationalCentralLog p).comp (1 - X ^ 2) -
        X ^ p * rationalLegendre (p / 6) * rationalProperJacobi (p / 6)) -
      C (rationalHarmonic (p / 6)) * rationalLegendre (p / 6) ^ 2 := by
    unfold centralRankHat; ring
  unfold centralGreenNumerator greenFunctional
  rw [hc, QO_sub_local, QO_C_mul, legendre_square_projection_zero p hp]
  ring

private theorem balancedGreenNumerator_eq_functional (hp : 19 ≤ p) :
    balancedGreenNumerator p hp = greenFunctional p (rankJacobiNode p 1)
      (balancedProperQ p hp) ((rationalCentralLog p).comp (1 - X ^ 2))
      (WPFirstResidue.LiteralNormalization.literalR0 p) := by
  have hc : balancedGreenJ p hp =
      C (2 : ℚ) * (rankJacobiNode p 1 ^ 2 * (rationalCentralLog p).comp (1 - X ^ 2) -
        X ^ p * rankJacobiNode p 1 * balancedProperQ p hp) +
      C (2 * (balancedProperQ p hp).eval 1) * rankJacobiNode p 1 ^ 2 := by
    unfold balancedGreenJ; simp only [_root_.map_ofNat, _root_.map_mul]; ring
  unfold balancedGreenNumerator greenFunctional
  rw [hc, QO_add, QO_C_mul, QO_C_mul,
    low_square_QO_zero p hp _ (actual_low_rankJacobi_degree p (by omega))]
  ring

noncomputable def greenTangentPolynomial (hp : 19 ≤ p) : (integralRationals p)[X] :=
  2 * integralLegendre p (p / 6) (by omega) * firstIncrement p hp * centralLogT p -
  X ^ p * (firstIncrement p hp * integralProperJacobi p (by omega) +
    integralLegendre p (p / 6) (by omega) * properIncrement p hp)
noncomputable def greenHigherPolynomial (hp : 19 ≤ p) : (integralRationals p)[X] :=
  firstIncrement p hp ^ 2 * centralLogT p -
    X ^ p * firstIncrement p hp * properIncrement p hp

noncomputable def greenCorrectionIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(2 * integralSixth p (by omega)) * QOi p hp (greenTangentPolynomial p hp) -
  QHi p hp (integralLegendre p (p / 6) (by omega) * firstIncrement p hp)
noncomputable def greenHigherIntegral (hp : 19 ≤ p) : integralRationals p :=
  -(2 * integralSixth p (by omega)) * QOi p hp (greenHigherPolynomial p hp) -
  integralHalf p (by omega) * QHi p hp (firstIncrement p hp ^ 2)

theorem greenCorrectionIntegral_value (hp : 19 ≤ p) :
    (greenCorrectionIntegral p hp).val =
      -QO p ((greenTangentPolynomial p hp).map (integralRationals p).subtype) / 3 -
      QH p ((integralLegendre p (p / 6) (by omega) * firstIncrement p hp).map
        (integralRationals p).subtype) := by
  change -(2 * (1 / 6 : ℚ)) * (QOi p hp (greenTangentPolynomial p hp)).val -
    (QHi p hp (integralLegendre p (p / 6) (by omega) * firstIncrement p hp)).val = _
  rw [QOi_value, QHi_value]; ring

theorem greenHigherIntegral_value (hp : 19 ≤ p) :
    (greenHigherIntegral p hp).val =
      -QO p ((greenHigherPolynomial p hp).map (integralRationals p).subtype) / 3 -
      QH p ((firstIncrement p hp ^ 2).map (integralRationals p).subtype) / 2 := by
  change -(2 * (1 / 6 : ℚ)) * (QOi p hp (greenHigherPolynomial p hp)).val -
    (1 / 2 : ℚ) * (QHi p hp (firstIncrement p hp ^ 2)).val = _
  rw [QOi_value, QHi_value]; ring

/-- Exact characteristic-zero identity before dividing by p. -/
theorem actual_balanced_green_taylor (hp : 19 ≤ p) :
    balancedGreenNumerator p hp = centralGreenNumerator p +
      (p : ℚ) * (greenCorrectionIntegral p hp).val +
      (p : ℚ) ^ 2 * (greenHigherIntegral p hp).val := by
  have hY := congrArg (fun P : (integralRationals p)[X] =>
    P.map (integralRationals p).subtype) (actual_first_increment_source p hp)
  simp only [balancedFirstIntegral_value, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_natCast, _root_.map_natCast, integralLegendre_value] at hY
  have hn := congrArg (fun P : (integralRationals p)[X] =>
    P.map (integralRationals p).subtype) (actual_proper_increment_source p hp)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_natCast, _root_.map_natCast,
    integralProperJacobi_value] at hn
  rw [balancedGreenNumerator_eq_functional p hp,
    centralGreenNumerator_eq_functional p hp, hY,
    show balancedProperQ p hp = rationalProperJacobi (p / 6) +
      C (p : ℚ) * (properIncrement p hp).map (integralRationals p).subtype from hn,
    greenCorrectionIntegral_value p hp, greenHigherIntegral_value p hp]
  simp only [greenTangentPolynomial, greenHigherPolynomial, centralLogT,
    Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_comp, Polynomial.map_one, integralLegendre_value,
    integralProperJacobi_value, integralCentralLog_value p hp]
  exact greenFunctional_taylor p _ _ _ _ _ _

noncomputable def actualTangentGroup (hp : 19 ≤ p) : ZMod p :=
  2 * QO p (X ^ p * ActualNextHermite.actualC p hp +
    actualVariationField p (by omega) * actualRankDividedField p (by omega)) / 9 +
  QH p (actualLegendreJacobi p * actualVariationField p (by omega)) / 3

private theorem actual_YA_projection_zero (hp : 19 ≤ p) :
    QO p (actualLegendreJacobi p * actualVariationField p (by omega)) = 0 := by
  unfold QO
  exact low_correction_both_projections_zero p hp _
    (NativeOriginalResidues.quadraticInverse_degree_of_le _ (p / 6)
      ((natDegree_mul_le_of_le (actualLegendreJacobi_degree p)
        (actualVariationField_degree p (by omega))).trans (by omega))) 0

private theorem actual_green_tangent_polynomial_field (hp : 19 ≤ p) :
    (greenTangentPolynomial p hp).map (residueHom p) =
      -C (1 / 3 : ZMod p) *
        (X ^ p * ActualNextHermite.actualC p hp +
         actualVariationField p (by omega) * actualRankDividedField p (by omega) +
         C (fieldHarmonic p (p / 6)) *
           (actualLegendreJacobi p * actualVariationField p (by omega))) := by
  let Y := actualLegendreJacobi p
  let A := actualVariationField p (by omega : 7 ≤ p)
  let n := properLegendreJacobi p
  let N1 := actualN1 p
  let h := fieldHarmonic p (p / 6)
  let L := (centralLogT p).map (residueHom p)
  have hR : actualRankDividedField p (by omega : 7 ≤ p) =
      Y * (L - C h) - X ^ p * n := by
    rw [← centralHatIntegral_field p hp]
    simp only [centralHatIntegral, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      integralLegendre_field, integralProperJacobi_field,
      integralHarmonic_field p (p / 6) (by omega), Y, L, h, n]
  have hC : ActualNextHermite.actualC p hp = Y * N1 + C (1 / 2 : ZMod p) * n * A := by
    exact (actual_Cmetric_eq_actualC p hp).symm
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h63 : (2 : (ZMod p)[X]) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p) := by
    change C (2 : ZMod p) * C (1 / 6 : ZMod p) = C (1 / 3 : ZMod p)
    rw [← C_mul]; congr 1; field_simp [h3, h6]; ring
  have h36 : C (1 / 3 : ZMod p) * C (1 / 2 : ZMod p) = C (1 / 6 : ZMod p) := by
    rw [← C_mul]; congr 1; field_simp [h2, h3, h6]; ring
  simp only [greenTangentPolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    Polynomial.map_X, integralLegendre_field, integralProperJacobi_field,
    firstIncrement_field p hp, properIncrement_field p hp]
  rw [hR, hC]
  change 2 * Y * (-C (1 / 6 : ZMod p) * A) * L -
    X ^ p * ((-C (1 / 6 : ZMod p) * A) * n + Y * (C (1 / 3 : ZMod p) * N1)) =
    -C (1 / 3 : ZMod p) *
      (X ^ p * (Y * N1 + C (1 / 2 : ZMod p) * n * A) +
        A * (Y * (L - C h) - X ^ p * n) + C h * (Y * A))
  linear_combination (X ^ p * n * A - Y * A * L) * h63 + (X ^ p * n * A) * h36

/-- The actual TC4 scalar is the residue of the fixed rational Green tangent. -/
theorem greenCorrectionIntegral_field (hp : 19 ≤ p) :
    residueHom p (greenCorrectionIntegral p hp) = actualTangentGroup p hp / 2 := by
  have hprod :
      (integralLegendre p (p / 6) (by omega) * firstIncrement p hp).map (residueHom p) =
      -C (1 / 6 : ZMod p) *
        (actualLegendreJacobi p * actualVariationField p (by omega)) := by
    rw [Polynomial.map_mul, integralLegendre_field, firstIncrement_field p hp]
    ring
  rw [greenCorrectionIntegral]
  simp only [_root_.map_sub, _root_.map_mul, _root_.map_neg, _root_.map_ofNat, integralSixth_field,
    QOi_field, QHi_field]
  rw [actual_green_tangent_polynomial_field p hp, hprod]
  simp only [← C_neg, QO_C_mul, QH_C_mul, QO_add,
    actual_YA_projection_zero p hp, mul_zero, add_zero]
  unfold actualTangentGroup
  simp only [QO_add]
  have h2 : (2 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have h9 : (9 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 9 (by omega) (by omega)
  field_simp [h2, h3, h6, h9]
  ring

/-- Its Q value is the fixed balancedGreenNumerator/p, not a carry packet. -/
noncomputable def balancedGreenDigitIntegral (hp : 19 ≤ p) : integralRationals p :=
  centralGreenDigitIntegral p hp + greenCorrectionIntegral p hp +
    (p : integralRationals p) * greenHigherIntegral p hp

theorem balancedGreenDigitIntegral_value (hp : 19 ≤ p) :
    (balancedGreenDigitIntegral p hp).val = balancedGreenNumerator p hp / (p : ℚ) := by
  change (centralGreenDigitIntegral p hp).val + (greenCorrectionIntegral p hp).val +
    (p : ℚ) * (greenHigherIntegral p hp).val = _
  rw [centralGreenDigitIntegral_value p hp, actual_balanced_green_taylor p hp]
  have hpq : (p : ℚ) ≠ 0 := by positivity
  field_simp [hpq]

theorem actual_balanced_green_digit_integral (hp : 19 ≤ p) :
    balancedGreenNumerator p hp / (p : ℚ) ∈ integralRationals p := by
  rw [← balancedGreenDigitIntegral_value p hp]
  exact (balancedGreenDigitIntegral p hp).property

/-- SB71c: actual evaluated eta=p/3, with the explicit p² remainder consumed. -/
theorem actual_SB71c (hp : 19 ≤ p) :
    residueHom p (balancedGreenDigitIntegral p hp) =
      residueHom p (centralGreenDigitIntegral p hp) + actualTangentGroup p hp / 2 := by
  simp only [balancedGreenDigitIntegral, _root_.map_add, _root_.map_mul, _root_.map_natCast,
    ZMod.natCast_self, zero_mul, add_zero, greenCorrectionIntegral_field p hp]

/-- SB71d for the canonical actual Dhat and the literal balanced Green numerator. -/
theorem actual_SB71d (hp : 19 ≤ p) :
    residueHom p (hatDigitIntegral p hp) + actualTangentGroup p hp / 2 =
      residueHom p (balancedGreenDigitIntegral p hp) +
        QO p (actualLegendreJacobi p ^ 2 *
          (actualSecondLogField p).comp (1 - X ^ 2)) / 3 := by
  rw [actual_hat_central_green_digit p hp, actual_SB71c p hp]
  ring

end WPFieldAssembly.ActualBalancedNodeAttachment
