import WPFieldAssembly.ActualSigmaIntegral
import WPFieldAssembly.ActualWeightedF0Carry
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
  WPPIntegralReduction WPFieldAssembly.ActualBalancedTrace
  WPFieldAssembly.ActualSigmaIntegral WPFieldAssembly.ActualHFTransmutation
  WPFieldAssembly.ActualGreenPrimitive WPFieldAssembly.ActualBalancedNodeAttachment
  WPFieldAssembly.NativeOriginalResidues WPFieldAssembly.NativeQuadraticInverse
  WPActualRankTwoHatLift WPActualGaussBottom
  WPFieldAssembly.ActualGreenCommonTrace WPFieldAssembly.ActualBalancedGreenTransfer
  WPFieldAssembly.ActualRationalPhaseCarry WPFieldAssembly.ActualSB101Trace

namespace WPFieldAssembly.SourceClosureBalancedFirstSource

set_option maxHeartbeats 1600000

theorem derivative_coefficientMap {R S : Type*} [Field R] [Field S]
    (f : R →+* S) (L : R[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (D L) =
      D (WPActualChiSource.coefficientMap f L) := by
  ext j
  rw [WPActualChiSource.coefficientMap_coeff, D_coeff, D_coeff,
    WPActualChiSource.coefficientMap_coeff, map_mul, map_intCast]

private noncomputable def nativeRingD {R : Type*} [CommRing R] :
    R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  (Finsupp.linearCombination R (fun n : ℤ => LaurentPolynomial.C (n : R) * T (n-1))).comp
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

private theorem nativeRingD_monomial {R : Type*} [CommRing R] (a : R) (n : ℤ) :
    nativeRingD (LaurentPolynomial.C a*T n) =
      LaurentPolynomial.C (a*(n : R))*T (n-1) := by
  rw [←single_eq_C_mul_T]
  change Finsupp.linearCombination R _ (Finsupp.single n a) = _
  rw [Finsupp.linearCombination_single, LaurentPolynomial.smul_eq_C_mul,
    ←mul_assoc, ←map_mul]

private theorem integral_derivative_map {R K : Type*} [CommRing R] [Field K]
    (f : R →+* K) (L : R[T;T⁻¹]) :
    WPActualChiSource.coefficientMap f (nativeRingD L) =
      D (WPActualChiSource.coefficientMap f L) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add, hL, hM]
  | C_mul_T n a =>
    rw [nativeRingD_monomial, WPActualChiSource.coefficientMap_monomial,
      WPActualChiSource.coefficientMap_monomial, D_monomial, map_mul, map_intCast]

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
private theorem lowFpullQ_value :
    ((squareQ p).comp WPActualPullbackSource.Vpolynomial).toLaurent=lowFpullQ p := rfl

private theorem product_first_source {R : Type*} [CommRing R]
    (a : ℕ → R) (t : R) (n : ℕ) :
    1-∏ j ∈ Finset.range n, (1-t*a j) =
      t*∑ j ∈ Finset.range n, a j*∏ k ∈ Finset.range j, (1-t*a k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    linear_combination ih

/-- The exact metric first carry is the finite telescoping source, before reduction. -/
noncomputable def metricFirstCarryIntegral (hp : 19 ≤ p) : integralRationals p :=
  ∑ j ∈ Finset.range (p/6),
    (2*WPActualRankTwoLowTaylor.integralSixth p (by omega)*smallIntegralInverse p (j+1)) *
      ∏ k ∈ Finset.range j, (1-smallIntegralInverse p (k+1)*etaStar p hp)

theorem actual_metric_whole_first_source (hp : 19 ≤ p) :
    1-metricStar p hp=(p : integralRationals p)*metricFirstCarryIntegral p hp := by
  have he := product_first_source
    (fun j => 2*WPActualRankTwoLowTaylor.integralSixth p (by omega)*smallIntegralInverse p (j+1))
    (p : integralRationals p) (p/6)
  have hfactor (j : ℕ) : (p : integralRationals p)*
      (2*WPActualRankTwoLowTaylor.integralSixth p (by omega)*smallIntegralInverse p (j+1))=
      smallIntegralInverse p (j+1)*etaStar p hp := by
    rw [etaStar]
    ring
  simp only [hfactor] at he
  simpa only [metricStar, metricFirstCarryIntegral] using he

theorem actual_metric_first_carry_field (hp : 19 ≤ p) :
    residueHom p (metricFirstCarryIntegral p hp)=
      (1/3 : ZMod p)*fieldHarmonic p (p/6) := by
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h6 : (6 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 6 (by omega) (by omega)
  have hscale : residueHom p (2*WPActualRankTwoLowTaylor.integralSixth p (by omega))=
      (1/3 : ZMod p) := by
    rw [map_mul, map_ofNat, WPActualRankTwoLowTaylor.integralSixth_field]
    field_simp [h3,h6]
    ring
  simp only [metricFirstCarryIntegral, map_sum, map_mul, map_prod,
    map_sub, map_one, etaStar_field, mul_zero, sub_zero,
    Finset.prod_const_one, mul_one, hscale]
  rw [←Finset.mul_sum, ←map_sum, ←integralHarmonic,
    integralHarmonic_field p (p/6) (by omega)]

/-- The actual evaluated Jacobi metric, cleared in the original x coordinate.
The p term and the metric and eta forcings remain literal over Q. -/
theorem actual_CB_metric_cleared_Q (hp : 19 ≤ p) :
    2 * (X+1) * (WPFiniteZSource.Abar : ℚ[X]) *
        (((squareQ p).comp WPActualPullbackSource.Vpolynomial) *
            (greenCBq p hp).derivative -
          greenCBq p hp * ((squareQ p).comp WPActualPullbackSource.Vpolynomial).derivative) -
      Polynomial.C (p : ℚ) * WPFiniteZSource.Abar *
        ((squareQ p).comp WPActualPullbackSource.Vpolynomial) * greenCBq p hp =
      3 * (X+1) * (greenCoordinateQ p)^((p-1)/2) *
        ((squareQ p).comp WPActualPullbackSource.Vpolynomial) *
          (1 - Polynomial.C ((metricStar p hp).val) *
              ((squareQ p).comp WPActualPullbackSource.Vpolynomial) +
            Polynomial.C ((etaStar p hp).val) *
              (greenTBq p hp).comp WPActualPullbackSource.Vpolynomial) := by
  let Y : ℚ[X] := WPActualRankTwoParameter.rankJacobiNode p 1
  let n : ℚ[X] := balancedProperQ p hp
  let B : ℚ[X] := greenBq p hp
  let F : ℚ[X] := Y^2
  let q : ℚ[X] := 1-X^2
  let b : ℚ[X] := 4*X^2-1
  let T : ℚ[X] := WPFiniteCubicLog.Tc
  let x : ℚ[X] := greenConicQ p
  let f : ℚ[X] := (squareQ p).comp WPActualPullbackSource.Vpolynomial
  let c : ℚ[X] := greenCBq p hp
  have hB : B=Y*n := by
    simp only [B, Y, n, greenBq, greenBIntegral, Polynomial.map_mul,
      balancedFirstIntegral_value, balancedProperQ]
  have hmetric := congrArg (Polynomial.map (integralRationals p).subtype)
    (actual_evaluated_normalized_metric p hp)
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one,
    ←Polynomial.derivative_map, balancedFirstIntegral_value] at hmetric
  change (1-X^2) * (Y*n.derivative-Y.derivative*n) -
    Polynomial.C ((etaStar p hp).val) * X * Y * n =
      1-Polynomial.C ((metricStar p hp).val)*Y^2 at hmetric
  have hproduct : q*(F*B.derivative-B*F.derivative)=
      F*(1-Polynomial.C ((metricStar p hp).val)*F+Polynomial.C ((etaStar p hp).val)*X*B) := by
    rw [hB]
    dsimp only [q, F]
    simp only [derivative_mul, derivative_sq, C_ofNat]
    linear_combination Y^2*hmetric
  have hYe : Y.comp (-X)=Polynomial.C ((-1 : ℚ)^(p/6))*Y := by
    have he := congrArg (Polynomial.map (integralRationals p).subtype)
      (greenBalancedFirst_reflect p hp)
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C] at he
    simpa only [Polynomial.map_neg, Polynomial.map_X, map_pow, map_neg, map_one,
      balancedFirstIntegral_value, Y] using he
  have hFe : F.comp (-X)=F := by
    simp only [F, pow_comp, hYe, mul_pow, ← C_pow, sign_square, C_1, one_mul]
  have hFq : (squareQ p).comp q=F := by
    change (quadraticInverse F).comp (1-X^2)=F
    exact quadraticInverse_even_pullback F (by norm_num) hFe
  have hV : WPActualPullbackSource.Vpolynomial.comp x=1-T^2 := by
    have h125 : (125 : ℚ[X])*Polynomial.C (1/125 : ℚ)=1 := by
      change Polynomial.C (125 : ℚ)*Polynomial.C (1/125 : ℚ)=Polynomial.C 1
      rw [←Polynomial.C_mul]
      norm_num
    dsimp only [WPActualPullbackSource.Vpolynomial, x, greenConicQ,
      T, WPFiniteCubicLog.Tc]
    simp only [mul_comp, C_comp, sub_comp, ofNat_comp, pow_comp, one_comp, X_comp]
    linear_combination (1-(4*X^3-3*X)^2)*h125
  have hf : f.comp x=F.comp T := by
    dsimp only [f]
    rw [comp_assoc, hV]
    rw [show 1-T^2=q.comp T by simp only [q, sub_comp, one_comp, pow_comp, X_comp]]
    rw [← comp_assoc, hFq]
  have hc : c.comp x=Polynomial.C (1/5 : ℚ)*X^p*B.comp T :=
    (green_actual_carrier_pullbacks_Q p hp).2
  have hdx : x.derivative=10*X := by
    dsimp only [x, greenConicQ]
    norm_num [derivative_sub, derivative_mul, derivative_pow, C_ofNat]
    ring
  have hdT : T.derivative=3*b := by
    dsimp only [T, WPFiniteCubicLog.Tc, b]
    norm_num [derivative_sub, derivative_mul, derivative_pow, C_ofNat]
    ring
  have hdc := congrArg Polynomial.derivative hc
  rw [derivative_comp, hdx] at hdc
  simp only [derivative_mul, derivative_C, derivative_pow, derivative_X,
    derivative_comp, hdT, zero_mul, zero_add, mul_one] at hdc
  have hdf : 10*X*f.derivative.comp x=3*b*F.derivative.comp T := by
    calc
      10*X*f.derivative.comp x=(f.comp x).derivative := by
        simpa only [hdx] using (derivative_comp f x).symm
      _=(F.comp T).derivative := congrArg Polynomial.derivative hf
      _=3*b*F.derivative.comp T := by
        simpa only [hdT] using derivative_comp F T
  have hm := congrArg (fun P : ℚ[X] => P.comp T) hproduct
  have hqT : q.comp T=q*b^2 := by
    dsimp only [q, b, T, WPFiniteCubicLog.Tc]
    simp only [sub_comp, one_comp, pow_comp, X_comp]
    ring
  simp only [mul_comp, sub_comp, add_comp, C_comp, one_comp, X_comp, hqT] at hm
  have hTB : ((greenTBq p hp).comp WPActualPullbackSource.Vpolynomial).comp x=
      T*B.comp T := by
    rw [comp_assoc, hV]
    rw [show 1-T^2=q.comp T by simp only [q, sub_comp, one_comp, pow_comp, X_comp]]
    rw [← comp_assoc, greenTBq_pullback p hp]
    simp only [mul_comp, X_comp, B]
  have hs : (greenCoordinateQ p).comp x=X^2 := greenCoordinateQ_conic p
  have ha : (WPFiniteZSource.Abar : ℚ[X]).comp x=25*q*b := by
    dsimp only [WPFiniteZSource.Abar, x, greenConicQ, q, b]
    simp only [mul_comp, sub_comp, ofNat_comp, one_comp, X_comp]
    ring
  have hxp : x+1=5*X^2 := by dsimp only [x, greenConicQ]; ring
  have hpow : (X^2 : ℚ[X])^((p-1)/2)*X^2=X^(p+1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have hn := WPFiniteWSource.half_exponent p hp
    omega
  have hprev : (X : ℚ[X])^(p-1)*X=X^p := by
    rw [← pow_succ]
    congr 1
    omega
  have h5inv : (5 : ℚ[X])*Polynomial.C (1/5 : ℚ)=1 := by
    change Polynomial.C (5 : ℚ)*Polynomial.C (1/5 : ℚ)=Polynomial.C 1
    rw [←Polynomial.C_mul]
    norm_num
  have hcd : x.natDegree=2 := by
    dsimp only [x, greenConicQ]
    compute_degree
    norm_num
  apply ConicKernel.comp_injective_nonconstant
    x (by rw [hcd]; norm_num)
  simp only [mul_comp, sub_comp, add_comp, pow_comp, ofNat_comp, C_comp,
    one_comp, X_comp, ha, hs, hTB]
  norm_num only [Nat.cast_ofNat]
  rw [hxp]
  change (2 : ℚ[X])*(5*X^2)*(25*q*b)*
      (f.comp x*c.derivative.comp x-c.comp x*f.derivative.comp x)-
      Polynomial.C (p : ℚ)*(25*q*b)*f.comp x*c.comp x =
    (3 : ℚ[X])*(5*X^2)*(X^2)^((p-1)/2)*f.comp x*
      (1-Polynomial.C (metricStar p hp).val*f.comp x+
        Polynomial.C (etaStar p hp).val*(T*B.comp T))
  rw [hf,hc]
  have hpow' : (X^2 : ℚ[X])^((p-1)/2)*(5*X^2)=5*X^(p+1) := by
    linear_combination 5*hpow
  have hscale : (3 : ℚ[X])*(5*X^2)*(X^2)^((p-1)/2)=15*X^p*X := by
    calc
      _ = 3*((X^2)^((p-1)/2)*(5*X^2)) := by ring
      _ = 15*X^p*X := by rw [hpow',pow_succ]; ring
  rw [hscale]
  linear_combination
    25*X*q*b*(F.comp T)*hdc -
    25*X*q*b*(Polynomial.C (1/5 : ℚ)*X^p*B.comp T)*hdf +
    15*X^p*X*hm +
    25*Polynomial.C (1/5 : ℚ)*Polynomial.C (p : ℚ)*q*b*
      (F.comp T)*(B.comp T)*hprev +
    15*X^p*X*q*b^2*((F.comp T)*(B.derivative.comp T)-
      (F.derivative.comp T)*(B.comp T))*h5inv

omit [Fact p.Prime] in
private theorem actual_zeta_derivative_cleared_Q (hp : 19 ≤ p) :
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent * D (zetaQ p) =
      LaurentPolynomial.C (p : ℚ) * zetaQ p *
        (D (WPFiniteZSource.Abar : ℚ[X]).toLaurent -
          (WPFiniteZSource.Abar : ℚ[X]).toLaurent * T (-1)) := by
  let A : ℚ[T;T⁻¹] := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
  have hd := D_pow_nat A (p-1)
  rw [show p-1+1=p by omega] at hd
  have hT : D (T (-(p : ℤ)) : ℚ[T;T⁻¹]) =
      -LaurentPolynomial.C (p : ℚ) * T (-(p : ℤ)) * T (-1) := by
    have he := D_monomial (1 : ℚ) (-(p : ℤ))
    rw [mul_assoc, ←T_add]
    simpa only [map_one, one_mul, Int.cast_neg, Int.cast_natCast,
      map_neg, neg_mul, sub_eq_add_neg] using he
  have hpow : A^p=A^(p-1)*A := by rw [←pow_succ, show p-1+1=p by omega]
  unfold zetaQ
  rw [D_mul, D_C_mul, hT, hd, hpow]
  ring

/-- The actual local proper source in the original Laurent coordinate.
Its Gamma logarithm is cleared; the p derivative and both Jacobi forcings remain. -/
theorem actual_local_proper_G_source_Q (hp : 19 ≤ p) :
    let A : ℚ[T;T⁻¹] := (WPFiniteZSource.Abar : ℚ[X]).toLaurent
    let x : ℚ[T;T⁻¹] := T 1
    let L := 2*x*(x+1)*A
    let Gamma := x*A+2*x*(x+1)*D A-2*(x+1)*A
    let f := lowFpullQ p
    let G := zetaQ p*(greenCBq p hp).toLaurent
    L*(f*D G-G*D f)-LaurentPolynomial.C (p : ℚ)*Gamma*f*G =
      3*x*(x+1)*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)*f*
        (1-LaurentPolynomial.C ((metricStar p hp).val)*f+
          LaurentPolynomial.C ((etaStar p hp).val)*
            ((greenTBq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent) := by
  dsimp only
  have hm := congrArg (fun P : ℚ[X] => P.toLaurent) (actual_CB_metric_cleared_Q p hp)
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, map_one,
    Polynomial.toLaurent_X, Polynomial.toLaurent_C, ←D_toLaurent,
    lowFpullQ_value] at hm
  have hz := actual_zeta_derivative_cleared_Q p hp
  have ht : (T 1*T (-1) : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  rw [D_mul]
  linear_combination
    T 1*zetaQ p*hm+
    2*T 1*(T 1+1)*lowFpullQ p*(greenCBq p hp).toLaurent*hz-
    2*LaurentPolynomial.C (p : ℚ)*(T 1+1)*lowFpullQ p*zetaQ p*
      (greenCBq p hp).toLaurent*(WPFiniteZSource.Abar : ℚ[X]).toLaurent*ht

noncomputable def actualReflectedProperIntegral (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  (actualCBIntegral p hp).toLaurent + T (((p-1)/2 : ℕ) : ℤ) *
    invert (actualCBIntegral p hp).toLaurent

noncomputable def actualReflectedProperQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (integralRationals p).subtype
    (actualReflectedProperIntegral p hp)

noncomputable def actualZetaQ : ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (integralRationals p).subtype (actualZetaIntegral p)

noncomputable def actualLowMQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (integralRationals p).subtype (actualLowMIntegral p hp)

private theorem actualLowMQ_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualLowMIntegral p hp)=actualLowMQ p hp := rfl

private theorem actualZetaQ_value :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualZetaIntegral p)=actualZetaQ p := rfl

private theorem actualReflectedProperQ_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualReflectedProperIntegral p hp)=actualReflectedProperQ p hp := rfl

private theorem lowReflectionDefectQ_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualReflectionDefectIntegral p hp)=lowReflectionDefectQ p hp := rfl

/-- The entire proper first source is divided only over the rationals.
Its integral and field values below follow from the actual whole quotient. -/
noncomputable def actualBalancedProperSourceQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  LaurentPolynomial.C (1/(p : ℚ)) *
    (actualLowMQ p hp * D (actualZetaQ p * actualReflectedProperQ p hp) -
      actualZetaQ p * actualReflectedProperQ p hp * D (actualLowMQ p hp) +
      actualLowMQ p hp ^ 2 * actualBSourceQ p)

theorem actual_balanced_numeratorQ_factor (hp : 19 ≤ p) :
    actualBalancedNumeratorQ p hp =
      actualZetaQ p * actualReflectedProperQ p hp +
        actualLowMQ p hp * comparisonRational p hp := by
  simp only [actualBalancedNumeratorQ, actualBalancedNumeratorIntegral,
    actualReflectedProperQ, actualReflectedProperIntegral, actualZetaQ,
    actualLowMQ, comparisonRational, map_add, map_mul]

/-- Exact differentiation of the original rational numerator, before reduction.
The comparison derivative contributes its actual divided sigma. -/
theorem actual_balanced_first_sourceQ (hp : 19 ≤ p) :
    actualLowMQ p hp * D (actualBalancedDividedQ p hp) -
      actualBalancedDividedQ p hp * D (actualLowMQ p hp) =
        actualBalancedProperSourceQ p hp + actualLowMQ p hp ^ 2 * actualSigmaQ p hp := by
  rw [actualBalancedDividedQ, actual_balanced_numeratorQ_factor p hp]
  simp only [actualBalancedProperSourceQ, actualSigmaQ, D_mul, D_C,
    zero_mul, zero_add, map_add]
  ring

/-- This gives the literal first-source numerator an integral witness;
no value is obtained by cancelling the field image of p. -/
theorem actualBalancedProperSourceQ_integral (hp : 19 ≤ p) :
    actualBalancedProperSourceQ p hp ∈ WPActualEtaIntegrality.integralLaurent p := by
  have he : WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualLowMIntegral p hp * nativeRingD (actualBalancedDividedIntegral p hp) -
        actualBalancedDividedIntegral p hp * nativeRingD (actualLowMIntegral p hp) -
        actualLowMIntegral p hp ^ 2 * actualSigmaIntegral p hp) =
      actualBalancedProperSourceQ p hp := by
    simp only [map_sub, map_mul, map_pow, integral_derivative_map,
      actualBalancedDividedIntegral_value, actualSigmaIntegral_value,
      actualLowMQ_value]
    linear_combination actual_balanced_first_sourceQ p hp
  rw [← he]
  exact mapped_integral p _

noncomputable def actualBalancedProperSourceIntegral (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  WPLaurentIntegralResidue.integralLift p
    ⟨actualBalancedProperSourceQ p hp, actualBalancedProperSourceQ_integral p hp⟩

theorem actualBalancedProperSourceIntegral_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualBalancedProperSourceIntegral p hp) = actualBalancedProperSourceQ p hp :=
  WPLaurentIntegralResidue.integralLift_rational p _

/-- The same whole first source holds integrally, with the actual sigma lift. -/
theorem actual_balanced_first_sourceIntegral (hp : 19 ≤ p) :
    actualLowMIntegral p hp * nativeRingD (actualBalancedDividedIntegral p hp) -
      actualBalancedDividedIntegral p hp * nativeRingD (actualLowMIntegral p hp) =
        actualBalancedProperSourceIntegral p hp +
          actualLowMIntegral p hp ^ 2 * actualSigmaIntegral p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (integralRationals p).subtype Subtype.val_injective
  simp only [map_sub, map_mul, map_add, map_pow, integral_derivative_map,
    actualBalancedDividedIntegral_value, actualBalancedProperSourceIntegral_value,
    actualSigmaIntegral_value, actualLowMQ_value]
  exact actual_balanced_first_sourceQ p hp

noncomputable def actualBalancedField (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (residueHom p) (actualBalancedDividedIntegral p hp)

noncomputable def actualBalancedProperSourceField (hp : 19 ≤ p) : (ZMod p)[T;T⁻¹] :=
  WPActualChiSource.coefficientMap (residueHom p) (actualBalancedProperSourceIntegral p hp)

private theorem actualBalancedField_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p)
      (actualBalancedDividedIntegral p hp)=actualBalancedField p hp := rfl

private theorem actualBalancedProperSourceField_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p)
      (actualBalancedProperSourceIntegral p hp)=actualBalancedProperSourceField p hp := rfl

private theorem residue_prime_constant :
    WPActualChiSource.coefficientMap (residueHom p)
      (LaurentPolynomial.C (p : integralRationals p))=0 := by
  rw [WPActualChiSource.coefficientMap_C, map_natCast, ZMod.natCast_self, map_zero]

/-- The native low local and reflected multipliers have the same field,
by the genuine integral first reflection source. -/
theorem actual_low_multiplier_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p) (actualLowMIntegral p hp) =
      WPActualChiSource.coefficientMap (residueHom p) (actualLowFIntegral p hp) := by
  have he := congrArg (WPActualChiSource.coefficientMap (residueHom p))
    (actual_low_reflection_defect_source p hp)
  change WPActualChiSource.coefficientMap (residueHom p)
      (actualLowFIntegral p hp - actualLowMIntegral p hp) =
    WPActualChiSource.coefficientMap (residueHom p)
      (LaurentPolynomial.C (p : integralRationals p) * actualReflectionDefectIntegral p hp) at he
  simp only [map_sub, map_mul, residue_prime_constant, zero_mul] at he
  exact (sub_eq_zero.mp he).symm

/-- Unconditional native Wronskian source of the original divided carrier.
The proper field source remains its specified entire rational first carry;
its closed SB99 native forcing is a subsequent attachment. -/
theorem actual_balanced_first_sourceField (hp : 19 ≤ p) :
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent * D (actualBalancedField p hp) -
      actualBalancedField p hp * D (NativeChiFieldSource.halfPullbackField p hp).toLaurent =
        actualBalancedProperSourceField p hp +
          (NativeChiFieldSource.halfPullbackField p hp).toLaurent ^ 2 *
            WPActualChiSource.coefficientMap (residueHom p) (actualSigmaIntegral p hp) := by
  have he := congrArg (WPActualChiSource.coefficientMap (residueHom p))
    (actual_balanced_first_sourceIntegral p hp)
  simp only [map_sub, map_mul, map_add, map_pow, integral_derivative_map,
    actual_low_multiplier_field p hp, actualLowFIntegral_field p hp,
    actualBalancedField_value, actualBalancedProperSourceField_value] at he
  exact he

noncomputable def nativeClearingL {R : Type*} [CommRing R] : R[T;T⁻¹] :=
  2*T 1*(T 1+1)*((4-X)*(4*X-1) : R[X]).toLaurent

omit [Fact p.Prime] in
/-- The actual clearing factor can be cancelled over every characteristic-p field. -/
theorem nativeClearingL_ne_zero {K : Type*} [Field K] [CharP K p] (hp : 19≤p) :
    (nativeClearingL : K[T;T⁻¹])≠0 := by
  let Q : K[X] := 2*X*(X+1)*WPFiniteZSource.Abar
  have hL : (nativeClearingL : K[T;T⁻¹])=Q.toLaurent := by
    simp only [nativeClearingL,Q,WPFiniteZSource.Abar,map_mul,map_add,map_ofNat,
      Polynomial.toLaurent_X,map_one]
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h36 : (36 : K)≠0 := by
    rw [show (36 : K)=2^2*3^2 by ring]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have hval : Q.eval 1=36 := by
    simp only [Q,WPFiniteZSource.Abar,eval_mul,eval_add,eval_sub,
      eval_ofNat,eval_X,eval_one]
    ring
  intro hz
  have hzQ : Q=0 := Polynomial.toLaurent_injective
    (by simpa only [map_zero] using hL.symm.trans hz)
  have he := congrArg (fun P : K[X] => P.eval 1) hzQ
  rw [hval,eval_zero] at he
  exact h36 he

noncomputable def nativeClearingGamma {R : Type*} [CommRing R] : R[T;T⁻¹] :=
  -12*T 3+9*T 2+4*T 1+8

noncomputable def nativeProperUQ : ℚ[T;T⁻¹] :=
  3*T 1*(T 1+1)*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)

noncomputable def nativeProperGQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  zetaQ p*(greenCBq p hp).toLaurent

noncomputable def nativeProperHQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ)*invert (nativeProperGQ p hp)

noncomputable def nativeTBQ (hp : 19 ≤ p) : ℚ[T;T⁻¹] :=
  ((greenTBq p hp).comp WPActualPullbackSource.Vpolynomial).toLaurent

private theorem clearing_Gamma_derivative :
    (nativeClearingGamma : ℚ[T;T⁻¹]) =
      T 1*(WPFiniteZSource.Abar : ℚ[X]).toLaurent+
      2*T 1*(T 1+1)*D (WPFiniteZSource.Abar : ℚ[X]).toLaurent-
      2*(T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent := by
  rw [D_toLaurent]
  simp [nativeClearingGamma, WPFiniteZSource.Abar, Polynomial.toLaurent_X]
  have h2 : (T 2 : ℚ[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
  have h3 : (T 3 : ℚ[T;T⁻¹])=T 1^3 := by rw [T_pow]; norm_num
  have hfour : (4 : ℚ[X]).toLaurent=(4 : ℚ[T;T⁻¹]) := by
    change (Polynomial.C (4 : ℚ)).toLaurent=(4 : ℚ[T;T⁻¹])
    simp only [map_ofNat]
  rw [hfour,h2,h3]
  ring

private theorem clearing_inversion {K : Type*} [Field K] :
    invert (nativeClearingL : K[T;T⁻¹])=T (-5)*nativeClearingL ∧
      T 3*invert (nativeClearingGamma : K[T;T⁻¹]) =
        -nativeClearingGamma+(T 1+1)*(WPFiniteZSource.Abar : K[X]).toLaurent := by
  have ha := Abar_invert (K := K)
  change invert (2*T 1*(T 1+1)*(WPFiniteZSource.Abar : K[X]).toLaurent)=
      T (-5)*(2*T 1*(T 1+1)*(WPFiniteZSource.Abar : K[X]).toLaurent) ∧ _
  constructor
  · have hl4 : (T (-1)*T (-1)*T (-2) : K[T;T⁻¹])=T (-4) := by
      rw [←T_add, ←T_add]; norm_num
    have hl3 : (T (-1)*T (-2) : K[T;T⁻¹])=T (-3) := by rw [←T_add]; norm_num
    have hr4 : (T (-5)*T 1 : K[T;T⁻¹])=T (-4) := by rw [←T_add]; norm_num
    have hr3 : (T (-5)*T 1*T 1 : K[T;T⁻¹])=T (-3) := by
      rw [←T_add, ←T_add]; norm_num
    simp only [map_mul, map_add, map_ofNat, map_one, invert_T, ha]
    linear_combination
      2*(WPFiniteZSource.Abar : K[X]).toLaurent*hl4+
      2*(WPFiniteZSource.Abar : K[X]).toLaurent*hl3-
      2*(WPFiniteZSource.Abar : K[X]).toLaurent*hr4-
      2*(WPFiniteZSource.Abar : K[X]).toLaurent*hr3
  · have h30 : (T 3*T (-3) : K[T;T⁻¹])=1 := by rw [←T_add]; norm_num
    have h31 : (T 3*T (-2) : K[T;T⁻¹])=T 1 := by rw [←T_add]; norm_num
    have h32 : (T 3*T (-1) : K[T;T⁻¹])=T 2 := by rw [←T_add]; norm_num
    have ht2 : (T 2 : K[T;T⁻¹])=T 1^2 := by rw [T_pow]; norm_num
    have ht3 : (T 3 : K[T;T⁻¹])=T 1^3 := by rw [T_pow]; norm_num
    have hA : (T 1+1)*(WPFiniteZSource.Abar : K[X]).toLaurent =
        -4*T 3+13*T 2+13*T 1-4 := by
      simp only [WPFiniteZSource.Abar, map_mul, map_sub, map_ofNat,
        Polynomial.toLaurent_X, map_one]
      rw [ht2,ht3]
      ring
    rw [hA]
    simp only [nativeClearingGamma, map_add, map_mul, map_neg, map_ofNat, invert_T]
    linear_combination -12*h30+9*h31+4*h32

omit [Fact p.Prime] in
private theorem zeta_inversion_Q : invert (zetaQ p)=zetaQ p := by
  have ht : (T (p : ℤ)*T (-2)^p : ℚ[T;T⁻¹])=T (-(p : ℤ)) := by
    rw [T_pow, ←T_add]
    congr 1
    omega
  simp only [zetaQ, map_mul, map_pow, invert_C, invert_T, neg_neg,
    Abar_invert, mul_pow]
  linear_combination
    (LaurentPolynomial.C (1/3 : ℚ)*LaurentPolynomial.C (1/5 : ℚ)^(2*(p-1)))*
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent^p*ht

omit [Fact p.Prime] in
private theorem proper_U_inversion_Q :
    invert (nativeProperUQ p)=
      T (-(((p-1)/2 : ℕ) : ℤ)-3)*nativeProperUQ p := by
  have hs : invert (greenCoordinateQ p).toLaurent=
      T (-1)*(greenCoordinateQ p).toLaurent := by
    have ht : (T (-1)*T 1 : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
    simp only [greenCoordinateQ, map_mul, map_add, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X, map_one, invert_C, invert_T]
    linear_combination -LaurentPolynomial.C (1/5 : ℚ)*ht
  have h0 : (T (-1)*T (-1)^((p-1)/2) : ℚ[T;T⁻¹])=
      T (-(((p-1)/2 : ℕ) : ℤ)-1) := by
    rw [T_pow, ←T_add]
    congr 1
    omega
  have h1 : (T (-1)*T (-1)*T (-1)^((p-1)/2) : ℚ[T;T⁻¹])=
      T (-(((p-1)/2 : ℕ) : ℤ)-2) := by
    rw [T_pow, ←T_add, ←T_add]
    congr 1
    omega
  have h2 : (T (-(((p-1)/2 : ℕ) : ℤ)-3)*T 1 : ℚ[T;T⁻¹])=
      T (-(((p-1)/2 : ℕ) : ℤ)-2) := by rw [←T_add]; congr 1; omega
  have h3 : (T (-(((p-1)/2 : ℕ) : ℤ)-3)*T 1*T 1 : ℚ[T;T⁻¹])=
      T (-(((p-1)/2 : ℕ) : ℤ)-1) := by
    rw [←T_add, ←T_add]
    congr 1
    omega
  simp only [nativeProperUQ, map_mul, map_add, map_pow, map_ofNat, map_one,
    invert_T, zeta_inversion_Q, hs, mul_pow]
  linear_combination
    3*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)*h0+
    3*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)*h1-
    3*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)*h2-
    3*zetaQ p*(greenCoordinateQ p).toLaurent^((p-1)/2)*h3

private theorem wronskian_inversion (n : ℤ) (F G : ℚ[T;T⁻¹]) :
    (T n*invert F)*D (T n*invert G)-(T n*invert G)*D (T n*invert F) =
      -T (2*n-2)*invert (F*D G-G*D F) := by
  have hd : D (T n : ℚ[T;T⁻¹])=LaurentPolynomial.C (n : ℚ)*T (n-1) := by
    simpa only [map_one, one_mul] using D_monomial (1 : ℚ) n
  have ht : (T n*T n*T (-2) : ℚ[T;T⁻¹])=T (2*n-2) := by
    rw [←T_add, ←T_add]
    congr 1
    omega
  simp only [D_mul, hd, D_invert, map_sub, map_mul]
  linear_combination -(invert F*invert (D G)-invert G*invert (D F))*ht

/-- The reflected actual proper source keeps the different logarithmic metric.
The shift derivative contributes the original -p/2 origin term. -/
theorem actual_reflected_proper_H_source_Q (hp : 19 ≤ p) :
    (nativeClearingL : ℚ[T;T⁻¹])*
        (actualLowMQ p hp*D (nativeProperHQ p hp)-
          nativeProperHQ p hp*D (actualLowMQ p hp))-
      LaurentPolynomial.C (p : ℚ)*
        (nativeClearingGamma-(T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent)*
          actualLowMQ p hp*nativeProperHQ p hp =
      -nativeProperUQ p*actualLowMQ p hp*
        (1-LaurentPolynomial.C ((metricStar p hp).val)*
          T (-(((p-1)/2 : ℕ) : ℤ))*actualLowMQ p hp+
          LaurentPolynomial.C ((etaStar p hp).val)*invert (nativeTBQ p hp)) := by
  let n : ℤ := (((p-1)/2 : ℕ) : ℤ)
  have hM : actualLowMQ p hp=T n*invert (lowFpullQ p) := by
    simp only [actualLowMQ, actualLowMIntegral, map_mul,
      WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert,
      actualLowFIntegral, WPActualChiSource.coefficientMap_toLaurent,
      Polynomial.map_comp, squareQIntegral_value p hp,
      WPHasseIntegralTransport.integralV_map_rational, lowFpullQ, n]
  have hlocal := actual_local_proper_G_source_Q p hp
  dsimp only at hlocal
  rw [←clearing_Gamma_derivative] at hlocal
  change nativeClearingL*(lowFpullQ p*D (nativeProperGQ p hp)-
      nativeProperGQ p hp*D (lowFpullQ p))-
      LaurentPolynomial.C (p : ℚ)*nativeClearingGamma*lowFpullQ p*nativeProperGQ p hp =
    nativeProperUQ p*lowFpullQ p*
      (1-LaurentPolynomial.C ((metricStar p hp).val)*lowFpullQ p+
        LaurentPolynomial.C ((etaStar p hp).val)*nativeTBQ p hp) at hlocal
  have hi := congrArg invert hlocal
  simp only [map_sub, map_mul, map_add, map_one, invert_C,
    (clearing_inversion (K := ℚ)).1, proper_U_inversion_Q] at hi
  have hw := wronskian_inversion n (lowFpullQ p) (nativeProperGQ p hp)
  rw [←nativeProperHQ] at hw
  simp only [map_sub, map_mul] at hw
  have hGamma := (clearing_inversion (K := ℚ)).2
  have hL : (T (2*n+3)*T (-5) : ℚ[T;T⁻¹])=T (2*n-2) := by
    rw [←T_add]; congr 1; omega
  have hU : (T (2*n+3)*T (-n-3) : ℚ[T;T⁻¹])=T n := by
    rw [←T_add]; congr 1; omega
  have h3 : (T (2*n+3) : ℚ[T;T⁻¹])=T 3*T n*T n := by
    rw [←T_add, ←T_add]; congr 1; omega
  have hunit : (T (-n)*T n : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
  rw [hM]
  change nativeClearingL*((T n*invert (lowFpullQ p))*D (nativeProperHQ p hp)-
      nativeProperHQ p hp*D (T n*invert (lowFpullQ p)))-
      LaurentPolynomial.C (p : ℚ)*
        (nativeClearingGamma-(T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent)*
        (T n*invert (lowFpullQ p))*nativeProperHQ p hp = _
  rw [hw]
  dsimp only [nativeProperHQ]
  linear_combination
    -T (2*n+3)*hi+
    -LaurentPolynomial.C (p : ℚ)*T n*T n*invert (lowFpullQ p)*
      invert (nativeProperGQ p hp)*hGamma+
    nativeClearingL*(invert (lowFpullQ p)*invert (D (nativeProperGQ p hp))-
      invert (nativeProperGQ p hp)*invert (D (lowFpullQ p)))*hL-
    nativeProperUQ p*invert (lowFpullQ p)*
      (1-LaurentPolynomial.C ((metricStar p hp).val)*invert (lowFpullQ p)+
        LaurentPolynomial.C ((etaStar p hp).val)*invert (nativeTBQ p hp))*hU-
    LaurentPolynomial.C (p : ℚ)*invert nativeClearingGamma*invert (lowFpullQ p)*
      invert (nativeProperGQ p hp)*h3-
    LaurentPolynomial.C ((metricStar p hp).val)*nativeProperUQ p*T n*
      invert (lowFpullQ p)^2*hunit

private theorem coupled_metric_algebra {R : Type*} [CommRing R]
    (a L Gamma U F M G H dF dM dG dH delta dDelta g kappa eta
      TB TBv phase half third Psrc B : R)
    (hwhole : a*Psrc=M*(dG+dH)-(G+H)*dM+M^2*B)
    (hdelta : F-M=a*delta) (hdDelta : dF-dM=a*dDelta)
    (hg : 1-g=a*kappa) (heta : eta=a*third)
    (hlocal : L*(F*dG-G*dF)-a*Gamma*F*G=U*F*(1-g*F+eta*TB))
    (hreflected : L*(M*dH-H*dM)-a*(Gamma-half)*M*H=
      -U*M*(1-g*phase*M+eta*TBv))
    (hB : L*B=U*(1-phase)) :
    a*(L*Psrc-
      (Gamma*(F*G+M*H)-half*M*H-L*delta*dG+L*G*dDelta+
        U*delta*(1-g*(M+F))+kappa*U*M^2*(1-phase)+
        third*U*(F*TB-M*TBv)))=0 := by
  have hM : M=F-a*delta := by linear_combination -hdelta
  have hdM : dM=dF-a*dDelta := by linear_combination -hdDelta
  have hgv : g=1-a*kappa := by linear_combination -hg
  simp only [hM,hdM,hgv,heta] at hwhole hlocal hreflected ⊢
  linear_combination L*hwhole+hlocal+hreflected+(F-a*delta)^2*hB

private theorem actual_low_F_rational_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (actualLowFIntegral p hp)=lowFpullQ p := by
  simp only [actualLowFIntegral, WPActualChiSource.coefficientMap_toLaurent,
    Polynomial.map_comp, squareQIntegral_value p hp,
    WPHasseIntegralTransport.integralV_map_rational, lowFpullQ]

private theorem actual_proper_sum_Q (hp : 19 ≤ p) :
    actualZetaQ p*actualReflectedProperQ p hp=
      nativeProperGQ p hp+nativeProperHQ p hp := by
  simp only [actualZetaQ, actual_zeta_rational_value p hp,
    actualReflectedProperQ, actualReflectedProperIntegral, map_add, map_mul,
    WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert,
    WPActualChiSource.coefficientMap_toLaurent, actual_CB_rational_value p hp,
    nativeProperGQ, nativeProperHQ, map_mul, zeta_inversion_Q]
  ring

private theorem actual_Bsource_cleared_Q :
    (nativeClearingL : ℚ[T;T⁻¹])*actualBSourceQ p=
      nativeProperUQ p*(1-T (-(((p-1)/2 : ℕ) : ℤ))) := by
  have hp0 := (Fact.out : p.Prime).pos
  have hA : (WPFiniteZSource.Abar : ℚ[X]).toLaurent^p=
      (WPFiniteZSource.Abar : ℚ[X]).toLaurent^(p-1)*
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent := by
    rw [←pow_succ, show p-1+1=p by omega]
  have hc : (2 : ℚ[T;T⁻¹])*LaurentPolynomial.C ((1/2 : ℚ)*(1/5 : ℚ)^(2*(p-1)))=
      3*LaurentPolynomial.C ((1/3 : ℚ)*(1/5 : ℚ)^(2*(p-1))) := by
    change LaurentPolynomial.C (2 : ℚ)*LaurentPolynomial.C _=
      LaurentPolynomial.C (3 : ℚ)*LaurentPolynomial.C _
    rw [←map_mul,←map_mul]
    congr 1
    ring
  change (2*T 1*(T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent)*actualBSourceQ p=_
  dsimp only [actualBSourceQ, nativeProperUQ, zetaQ]
  rw [hA]
  linear_combination T 1*(T 1+1)*T (-(p : ℤ))*
    (greenCoordinateQ p).toLaurent^((p-1)/2)*
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent^(p-1)*
    (WPFiniteZSource.Abar : ℚ[X]).toLaurent*
    (1-T (-(((p-1)/2 : ℕ) : ℤ)))*hc

/-- The complete proper first carry is reduced over Q from both actual metrics.
Division by p occurs only after its genuine reflection and metric first sources. -/
theorem actual_proper_first_carry_cleared_Q (hp : 19 ≤ p) :
    (nativeClearingL : ℚ[T;T⁻¹])*actualBalancedProperSourceQ p hp =
      nativeClearingGamma*(lowFpullQ p*nativeProperGQ p hp+
        actualLowMQ p hp*nativeProperHQ p hp)-
      LaurentPolynomial.C (1/2 : ℚ)*nativeClearingL*T (-1)*
        actualLowMQ p hp*nativeProperHQ p hp-
      nativeClearingL*lowReflectionDefectQ p hp*D (nativeProperGQ p hp)+
      nativeClearingL*nativeProperGQ p hp*D (lowReflectionDefectQ p hp)+
      nativeProperUQ p*lowReflectionDefectQ p hp*
        (1-LaurentPolynomial.C ((metricStar p hp).val)*(actualLowMQ p hp+lowFpullQ p))+
      LaurentPolynomial.C ((metricFirstCarryIntegral p hp).val)*nativeProperUQ p*
        actualLowMQ p hp^2*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+
      LaurentPolynomial.C (1/3 : ℚ)*nativeProperUQ p*
        (lowFpullQ p*nativeTBQ p hp-actualLowMQ p hp*invert (nativeTBQ p hp)) := by
  have hM : actualLowMQ p hp=
      T (((p-1)/2 : ℕ) : ℤ)*invert (lowFpullQ p) := by
    simp only [actualLowMQ, actualLowMIntegral, map_mul,
      WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert,
      actual_low_F_rational_value p hp]
  have hd := actual_low_reflection_source_Q p hp
  rw [←hM] at hd
  have hdd := congrArg D hd
  simp only [map_sub,D_C_mul] at hdd
  have hgQ := congrArg (integralRationals p).subtype
    (actual_metric_whole_first_source p hp)
  rw [map_sub, map_one, map_mul, map_natCast] at hgQ
  change 1-(metricStar p hp).val=
    (p : ℚ)*(metricFirstCarryIntegral p hp).val at hgQ
  have hg := congrArg (LaurentPolynomial.C : ℚ →+* ℚ[T;T⁻¹]) hgQ
  rw [map_sub, map_one, map_mul] at hg
  have heta : LaurentPolynomial.C ((etaStar p hp).val)=
      (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹])*LaurentPolynomial.C (1/3 : ℚ) := by
    rw [etaStar_value,←map_mul]
    congr 1
    ring
  have hh : (T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent =
      LaurentPolynomial.C (1/2 : ℚ)*nativeClearingL*T (-1) := by
    have ht : (T 1*T (-1) : ℚ[T;T⁻¹])=1 := by rw [←T_add]; norm_num
    have hc : (LaurentPolynomial.C (1/2 : ℚ) : ℚ[T;T⁻¹])*2=1 := by
      change LaurentPolynomial.C (1/2 : ℚ)*LaurentPolynomial.C 2=LaurentPolynomial.C 1
      rw [←map_mul]
      norm_num
    change (T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent=
      LaurentPolynomial.C (1/2 : ℚ)*(2*T 1*(T 1+1)*
        (WPFiniteZSource.Abar : ℚ[X]).toLaurent)*T (-1)
    linear_combination
      -(T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent*T 1*T (-1)*hc-
      (T 1+1)*(WPFiniteZSource.Abar : ℚ[X]).toLaurent*ht
  have hlocal := actual_local_proper_G_source_Q p hp
  dsimp only at hlocal
  rw [←clearing_Gamma_derivative] at hlocal
  change nativeClearingL*(lowFpullQ p*D (nativeProperGQ p hp)-
      nativeProperGQ p hp*D (lowFpullQ p))-
      LaurentPolynomial.C (p : ℚ)*nativeClearingGamma*lowFpullQ p*nativeProperGQ p hp =
    nativeProperUQ p*lowFpullQ p*
      (1-LaurentPolynomial.C ((metricStar p hp).val)*lowFpullQ p+
        LaurentPolynomial.C ((etaStar p hp).val)*nativeTBQ p hp) at hlocal
  have href := actual_reflected_proper_H_source_Q p hp
  rw [hh] at href
  have hpq : (p : ℚ)≠0 := by positivity
  have hpC : (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹])≠0 := by
    intro h
    apply hpq
    exact LaurentPolynomial.C.injective (h.trans (map_zero LaurentPolynomial.C).symm)
  have hwhole : LaurentPolynomial.C (p : ℚ)*actualBalancedProperSourceQ p hp=
      actualLowMQ p hp*(D (nativeProperGQ p hp)+D (nativeProperHQ p hp))-
        (nativeProperGQ p hp+nativeProperHQ p hp)*D (actualLowMQ p hp)+
        actualLowMQ p hp^2*actualBSourceQ p := by
    have hc : (LaurentPolynomial.C (p : ℚ) : ℚ[T;T⁻¹])*
        LaurentPolynomial.C (1/(p : ℚ))=1 := by
      rw [←map_mul, mul_one_div_cancel hpq, map_one]
    rw [actualBalancedProperSourceQ, ←mul_assoc, hc, one_mul,
      actual_proper_sum_Q p hp, map_add]
  have he := coupled_metric_algebra
    (LaurentPolynomial.C (p : ℚ)) nativeClearingL nativeClearingGamma (nativeProperUQ p)
    (lowFpullQ p) (actualLowMQ p hp) (nativeProperGQ p hp) (nativeProperHQ p hp)
    (D (lowFpullQ p)) (D (actualLowMQ p hp)) (D (nativeProperGQ p hp))
    (D (nativeProperHQ p hp)) (lowReflectionDefectQ p hp) (D (lowReflectionDefectQ p hp))
    (LaurentPolynomial.C ((metricStar p hp).val))
    (LaurentPolynomial.C ((metricFirstCarryIntegral p hp).val))
    (LaurentPolynomial.C ((etaStar p hp).val)) (nativeTBQ p hp) (invert (nativeTBQ p hp))
    (T (-(((p-1)/2 : ℕ) : ℤ)))
    (LaurentPolynomial.C (1/2 : ℚ)*nativeClearingL*T (-1))
    (LaurentPolynomial.C (1/3 : ℚ)) (actualBalancedProperSourceQ p hp) (actualBSourceQ p)
    hwhole hd hdd hg heta hlocal href (actual_Bsource_cleared_Q p)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hpC)

noncomputable def nativeProperGIntegral (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  actualZetaIntegral p*(actualCBIntegral p hp).toLaurent

noncomputable def nativeProperHIntegral (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  T (((p-1)/2 : ℕ) : ℤ)*invert (nativeProperGIntegral p hp)

noncomputable def nativeProperUIntegral : (integralRationals p)[T;T⁻¹] :=
  3*T 1*(T 1+1)*actualZetaIntegral p*(comparisonCoordinateI p).toLaurent^((p-1)/2)

noncomputable def nativeTBIntegral (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] :=
  ((quadraticInverse (X*greenBIntegral p hp)).comp
    (WPHasseIntegralTransport.integralV p (by omega))).toLaurent

private theorem clearing_coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) :
    WPActualChiSource.coefficientMap f (nativeClearingL : R[T;T⁻¹])=
      (nativeClearingL : S[T;T⁻¹]) ∧
    WPActualChiSource.coefficientMap f (nativeClearingGamma : R[T;T⁻¹])=
      (nativeClearingGamma : S[T;T⁻¹]) := by
  have hA : WPActualChiSource.coefficientMap f (((4-X)*(4*X-1) : R[X]).toLaurent)=
      ((4-X)*(4*X-1) : S[X]).toLaurent := by
    rw [WPActualChiSource.coefficientMap_toLaurent]
    congr 1
    simp only [Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_ofNat, Polynomial.map_X, Polynomial.map_one]
  constructor
  · change WPActualChiSource.coefficientMap f
      (2*T 1*(T 1+1)*((4-X)*(4*X-1) : R[X]).toLaurent)=
      2*T 1*(T 1+1)*((4-X)*(4*X-1) : S[X]).toLaurent
    rw [map_mul,hA]
    simp only [map_mul, map_add, map_ofNat, map_one,
      WPActualChiSource.coefficientMap_T]
  · simp only [nativeClearingGamma, map_add, map_mul, map_neg, map_ofNat,
      WPActualChiSource.coefficientMap_T]

theorem native_integral_sources_value (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (nativeProperGIntegral p hp)=nativeProperGQ p hp ∧
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (nativeProperHIntegral p hp)=nativeProperHQ p hp ∧
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (nativeProperUIntegral p)=nativeProperUQ p ∧
    WPActualChiSource.coefficientMap (integralRationals p).subtype
      (nativeTBIntegral p hp)=nativeTBQ p hp := by
  have hG : WPActualChiSource.coefficientMap (integralRationals p).subtype
      (nativeProperGIntegral p hp)=nativeProperGQ p hp := by
    simp only [nativeProperGIntegral, nativeProperGQ, map_mul,
      actual_zeta_rational_value p hp, WPActualChiSource.coefficientMap_toLaurent,
      actual_CB_rational_value p hp]
  have hs : (comparisonCoordinateI p).map (integralRationals p).subtype=greenCoordinateQ p := by
    simp only [comparisonCoordinateI, greenCoordinateQ, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
      Subring.subtype_apply, smallIntegralInverse_value p 5 (by omega) (by omega)]
    norm_num
  refine ⟨hG, ?_, ?_, ?_⟩
  · simp only [nativeProperHIntegral, nativeProperHQ, map_mul,
      WPActualChiSource.coefficientMap_T, WPActualChiSource.coefficientMap_invert, hG]
  · simp only [nativeProperUIntegral, nativeProperUQ, map_mul, map_add,
      map_ofNat, map_one, map_pow, WPActualChiSource.coefficientMap_T,
      actual_zeta_rational_value p hp, WPActualChiSource.coefficientMap_toLaurent,
      hs]
  · simp only [nativeTBIntegral, nativeTBQ, WPActualChiSource.coefficientMap_toLaurent,
      Polynomial.map_comp, quadraticInverse_map, Polynomial.map_mul, Polynomial.map_X,
      WPHasseIntegralTransport.integralV_map_rational, greenTBq, greenBq]

/-- The rational metric reduction has its exact original coefficient-ring witness.
Every reflected source, first metric carry and eta/p term remains present. -/
theorem actual_proper_first_carry_cleared_integral (hp : 19 ≤ p) :
    (nativeClearingL : (integralRationals p)[T;T⁻¹])*actualBalancedProperSourceIntegral p hp =
      nativeClearingGamma*(actualLowFIntegral p hp*nativeProperGIntegral p hp+
        actualLowMIntegral p hp*nativeProperHIntegral p hp)-
      LaurentPolynomial.C (smallIntegralInverse p 2)*nativeClearingL*T (-1)*
        actualLowMIntegral p hp*nativeProperHIntegral p hp-
      nativeClearingL*actualReflectionDefectIntegral p hp*nativeRingD (nativeProperGIntegral p hp)+
      nativeClearingL*nativeProperGIntegral p hp*nativeRingD (actualReflectionDefectIntegral p hp)+
      nativeProperUIntegral p*actualReflectionDefectIntegral p hp*
        (1-LaurentPolynomial.C (metricStar p hp)*(actualLowMIntegral p hp+actualLowFIntegral p hp))+
      LaurentPolynomial.C (metricFirstCarryIntegral p hp)*nativeProperUIntegral p*
        actualLowMIntegral p hp^2*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+
      LaurentPolynomial.C (smallIntegralInverse p 3)*nativeProperUIntegral p*
        (actualLowFIntegral p hp*nativeTBIntegral p hp-
          actualLowMIntegral p hp*invert (nativeTBIntegral p hp)) := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (integralRationals p).subtype Subtype.val_injective
  have hv := native_integral_sources_value p hp
  simp only [map_mul, map_sub, map_add, map_pow, map_one,
    (clearing_coefficientMap (integralRationals p).subtype).1,
    (clearing_coefficientMap (integralRationals p).subtype).2,
    actualBalancedProperSourceIntegral_value p hp, actual_low_F_rational_value p hp,
    hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, integral_derivative_map,
    WPActualChiSource.coefficientMap_C, WPActualChiSource.coefficientMap_T,
    WPActualChiSource.coefficientMap_invert,
    Subring.subtype_apply,
    smallIntegralInverse_value p 2 (by omega) (by omega),
    smallIntegralInverse_value p 3 (by omega) (by omega), actualLowMQ_value,
    lowReflectionDefectQ_value]
  exact actual_proper_first_carry_cleared_Q p hp

private theorem actual_proper_sum_integral (hp : 19 ≤ p) :
    actualZetaIntegral p*actualReflectedProperIntegral p hp=
      nativeProperGIntegral p hp+nativeProperHIntegral p hp := by
  apply WPLaurentIntegralResidue.coefficientMap_injective
    (integralRationals p).subtype Subtype.val_injective
  have hv := native_integral_sources_value p hp
  simp only [map_mul, map_add, actualZetaQ_value, actualReflectedProperQ_value, hv.1,hv.2.1]
  exact actual_proper_sum_Q p hp

/-- The actual local metric, after reducing the entire characteristic-zero source. -/
theorem actual_local_proper_metric_field (hp : 19 ≤ p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let G := WPActualChiSource.coefficientMap (residueHom p) (nativeProperGIntegral p hp)
    let U := WPActualChiSource.coefficientMap (residueHom p) (nativeProperUIntegral p)
    (nativeClearingL : (ZMod p)[T;T⁻¹])*(f*D G-G*D f)=U*f*(1-f) := by
  have hi : (nativeClearingL : (integralRationals p)[T;T⁻¹])*
        (actualLowFIntegral p hp*nativeRingD (nativeProperGIntegral p hp)-
          nativeProperGIntegral p hp*nativeRingD (actualLowFIntegral p hp))-
      LaurentPolynomial.C (p : integralRationals p)*nativeClearingGamma*
        actualLowFIntegral p hp*nativeProperGIntegral p hp =
      nativeProperUIntegral p*actualLowFIntegral p hp*
        (1-LaurentPolynomial.C (metricStar p hp)*actualLowFIntegral p hp+
          LaurentPolynomial.C (etaStar p hp)*nativeTBIntegral p hp) := by
    apply WPLaurentIntegralResidue.coefficientMap_injective
      (integralRationals p).subtype Subtype.val_injective
    have hv := native_integral_sources_value p hp
    simp only [map_mul, map_sub, map_add, map_one,
      (clearing_coefficientMap (integralRationals p).subtype).1,
      (clearing_coefficientMap (integralRationals p).subtype).2,
      actual_low_F_rational_value p hp, hv.1,hv.2.2.1,hv.2.2.2,
      integral_derivative_map, WPActualChiSource.coefficientMap_C, map_natCast,
      Subring.subtype_apply]
    rw [clearing_Gamma_derivative]
    exact actual_local_proper_G_source_Q p hp
  have he := congrArg (WPActualChiSource.coefficientMap (residueHom p)) hi
  have hpzero : residueHom p (p : integralRationals p)=0 := by
    rw [map_natCast,ZMod.natCast_self]
  simp only [map_mul, map_sub, map_add, map_one,
    (clearing_coefficientMap (residueHom p)).1,
    (clearing_coefficientMap (residueHom p)).2,
    actualLowFIntegral_field p hp, integral_derivative_map,
    WPActualChiSource.coefficientMap_C, hpzero,
    metricStar_field p hp, etaStar_field p hp, map_zero,
    zero_mul, sub_zero, add_zero, one_mul] at he
  exact he

/-- The original numerator seed is used only as an identity of the attached fields. -/
theorem actual_native_seed_field (hp : 19 ≤ p) :
    WPActualChiSource.coefficientMap (residueHom p) (nativeProperGIntegral p hp)+
      WPActualChiSource.coefficientMap (residueHom p) (nativeProperHIntegral p hp)+
      (NativeChiFieldSource.halfPullbackField p hp).toLaurent*
        WPActualChiSource.coefficientMap (residueHom p) (comparisonIntegral p)=0 := by
  have he := actualBalancedNumeratorIntegral_field_zero p hp
  change WPActualChiSource.coefficientMap (residueHom p)
    (actualZetaIntegral p*actualReflectedProperIntegral p hp+
      actualLowMIntegral p hp*comparisonIntegral p)=0 at he
  rw [actual_proper_sum_integral p hp] at he
  simpa only [map_add, map_mul, actual_low_multiplier_field p hp,
    actualLowFIntegral_field p hp] using he

/-- This is the genuine reduced proper first carry, with all SB99 forcings explicit. -/
theorem actual_proper_first_carry_cleared_field (hp : 19 ≤ p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let G := WPActualChiSource.coefficientMap (residueHom p) (nativeProperGIntegral p hp)
    let H := WPActualChiSource.coefficientMap (residueHom p) (nativeProperHIntegral p hp)
    let U := WPActualChiSource.coefficientMap (residueHom p) (nativeProperUIntegral p)
    let delta := WPActualChiSource.coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
    let TB := WPActualChiSource.coefficientMap (residueHom p) (nativeTBIntegral p hp)
    (nativeClearingL : (ZMod p)[T;T⁻¹])*actualBalancedProperSourceField p hp =
      nativeClearingGamma*(f*G+f*H)-LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*T (-1)*f*H-
      nativeClearingL*delta*D G+nativeClearingL*G*D delta+
      U*delta*(1-2*f)+LaurentPolynomial.C (1/3 : ZMod p)*LaurentPolynomial.C (fieldHarmonic p (p/6))*
        U*f^2*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+
      LaurentPolynomial.C (1/3 : ZMod p)*U*(f*TB-f*invert TB) := by
  let Φ : (integralRationals p)[T;T⁻¹] →+* (ZMod p)[T;T⁻¹] :=
    WPActualChiSource.coefficientMap (residueHom p)
  have transport
      (F M G H U delta TB A : (integralRationals p)[T;T⁻¹])
      (mu kappa a2 a3 : integralRationals p)
      (f : (ZMod p)[T;T⁻¹]) (k : ZMod p)
      (hF : Φ F=f) (hM : Φ M=f)
      (hmu : residueHom p mu=1)
      (hkappa : residueHom p kappa=(1/3 : ZMod p)*k)
      (ha2 : residueHom p a2=(1/2 : ZMod p))
      (ha3 : residueHom p a3=(1/3 : ZMod p))
      (hi :
        (nativeClearingL : (integralRationals p)[T;T⁻¹])*A =
          nativeClearingGamma*(F*G+M*H)-
          LaurentPolynomial.C a2*nativeClearingL*T (-1)*M*H-
          nativeClearingL*delta*nativeRingD G+
          nativeClearingL*G*nativeRingD delta+
          U*delta*(1-LaurentPolynomial.C mu*(M+F))+
          LaurentPolynomial.C kappa*U*M^2*
            (1-T (-(((p-1)/2 : ℕ) : ℤ)))+
          LaurentPolynomial.C a3*U*(F*TB-M*invert TB)) :
      (nativeClearingL : (ZMod p)[T;T⁻¹])*Φ A =
        nativeClearingGamma*(f*Φ G+f*Φ H)-
        LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*T (-1)*f*Φ H-
        nativeClearingL*Φ delta*D (Φ G)+
        nativeClearingL*Φ G*D (Φ delta)+
        Φ U*Φ delta*(1-2*f)+
        LaurentPolynomial.C (1/3 : ZMod p)*LaurentPolynomial.C k*
          Φ U*f^2*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+
        LaurentPolynomial.C (1/3 : ZMod p)*Φ U*
          (f*Φ TB-f*invert (Φ TB)) := by
    have he := congrArg Φ hi
    dsimp only [Φ] at he hF hM ⊢
    simpa only [map_mul, map_sub, map_add, map_pow, map_one,
      (clearing_coefficientMap (residueHom p)).1,
      (clearing_coefficientMap (residueHom p)).2,
      integral_derivative_map,
      WPActualChiSource.coefficientMap_C,
      WPActualChiSource.coefficientMap_T,
      WPActualChiSource.coefficientMap_invert,
      hF, hM, hmu, hkappa, ha2, ha3, one_mul, ←two_mul] using he
  have htwo :
      residueHom p (smallIntegralInverse p 2)=(1/2 : ZMod p) := by
    simpa only [Nat.cast_ofNat, one_div] using
      smallIntegralInverse_field p 2 (by omega) (by omega)
  have hthree :
      residueHom p (smallIntegralInverse p 3)=(1/3 : ZMod p) := by
    simpa only [Nat.cast_ofNat, one_div] using
      smallIntegralInverse_field p 3 (by omega) (by omega)
  exact transport
    (actualLowFIntegral p hp) (actualLowMIntegral p hp)
    (nativeProperGIntegral p hp) (nativeProperHIntegral p hp)
    (nativeProperUIntegral p) (actualReflectionDefectIntegral p hp)
    (nativeTBIntegral p hp) (actualBalancedProperSourceIntegral p hp)
    (metricStar p hp) (metricFirstCarryIntegral p hp)
    (smallIntegralInverse p 2) (smallIntegralInverse p 3)
    (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    (fieldHarmonic p (p/6))
    (actualLowFIntegral_field p hp)
    ((actual_low_multiplier_field p hp).trans
      (actualLowFIntegral_field p hp))
    (metricStar_field p hp)
    (actual_metric_first_carry_field p hp)
    htwo hthree
    (actual_proper_first_carry_cleared_integral p hp)

/-- The actual divided balanced carrier has the fully cleared SB99 native forcing.
This uses the seed only after its rational first carry and integral reduction. -/
theorem actual_native_first_source_cleared_field (hp : 19 ≤ p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let G := WPActualChiSource.coefficientMap (residueHom p) (nativeProperGIntegral p hp)
    let H := WPActualChiSource.coefficientMap (residueHom p) (nativeProperHIntegral p hp)
    let U := WPActualChiSource.coefficientMap (residueHom p) (nativeProperUIntegral p)
    let delta := WPActualChiSource.coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
    let TB := WPActualChiSource.coefficientMap (residueHom p) (nativeTBIntegral p hp)
    let S := WPActualChiSource.coefficientMap (residueHom p) (comparisonIntegral p)
    let sigma := WPActualChiSource.coefficientMap (residueHom p) (actualSigmaIntegral p hp)
    f*(nativeClearingL : (ZMod p)[T;T⁻¹])*
        (f*D (actualBalancedField p hp)-actualBalancedField p hp*D f) =
      -nativeClearingGamma*f^3*S-
      LaurentPolynomial.C (1/2 : ZMod p)*nativeClearingL*f^2*H*T (-1)+
      f*nativeClearingL*G*D delta-nativeClearingL*G*delta*D f-f^2*U*delta+
      LaurentPolynomial.C (1/3 : ZMod p)*LaurentPolynomial.C (fieldHarmonic p (p/6))*
        f^3*U*(1-T (-(((p-1)/2 : ℕ) : ℤ)))+
      LaurentPolynomial.C (1/3 : ZMod p)*f^2*U*(TB-invert TB)+f^3*nativeClearingL*sigma := by
  have hcarry := actual_proper_first_carry_cleared_field p hp
  have hmetric := actual_local_proper_metric_field p hp
  have hseed := actual_native_seed_field p hp
  have hfirst := actual_balanced_first_sourceField p hp
  dsimp only at hcarry hmetric ⊢
  let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
  let delta := WPActualChiSource.coefficientMap (residueHom p) (actualReflectionDefectIntegral p hp)
  linear_combination
    f*nativeClearingL*hfirst+f*hcarry-delta*hmetric+nativeClearingGamma*f^2*hseed

noncomputable def nativeFourUnitIntegral (hp : 19 ≤ p) : (integralRationals p)ˣ :=
  { val := 4
    inv := smallIntegralInverse p 4
    val_inv := by
      apply Subtype.ext
      change (4 : ℚ)*(smallIntegralInverse p 4).val=1
      rw [smallIntegralInverse_value p 4 (by omega) (by omega)]
      norm_num
    inv_val := by
      apply Subtype.ext
      change (smallIntegralInverse p 4).val*(4 : ℚ)=1
      rw [smallIntegralInverse_value p 4 (by omega) (by omega)]
      norm_num }

private theorem native_eval₂_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) (L : R[T;T⁻¹]) :
    f (LaurentPolynomial.eval₂ (RingHom.id R) u L)=
      LaurentPolynomial.eval₂ (RingHom.id S) (Units.map f.toMonoidHom u)
        (WPActualChiSource.coefficientMap f L) := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add,hL,hM]
  | C_mul_T n a =>
    rw [WPActualChiSource.coefficientMap_monomial,
      LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, map_mul]
    simp only [RingHom.id_apply]
    congr 1
    exact congrArg (fun v : Sˣ => (v : S)) (map_zpow (Units.map f.toMonoidHom) u n)

private theorem native_inversion_eval {R : Type*} [CommRing R]
    (u : Rˣ) (L : R[T;T⁻¹]) :
    LaurentPolynomial.eval₂ (RingHom.id R) u (invert L)=
      LaurentPolynomial.eval₂ (RingHom.id R) u⁻¹ L := by
  induction L using LaurentPolynomial.induction_on' with
  | add L M hL hM => simp only [map_add,hL,hM]
  | C_mul_T n a =>
    rw [map_mul, invert_C, invert_T, LaurentPolynomial.eval₂_C_mul_T,
      LaurentPolynomial.eval₂_C_mul_T]
    simp only [RingHom.id_apply, zpow_neg, inv_zpow]

private theorem actual_comparison_zero_ends_integral (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp) (comparisonIntegral p)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp)⁻¹ (comparisonIntegral p)=0 := by
  let v := nativeFourUnitIntegral p hp
  have hv : (v : integralRationals p)=4 := rfl
  have hvi : ((v⁻¹ : (integralRationals p)ˣ) : integralRationals p)=
      smallIntegralInverse p 4 := rfl
  have hs4 : (comparisonCoordinateI p).eval (v : integralRationals p)=1 := by
    simp only [comparisonCoordinateI, eval_mul, eval_C, eval_add, eval_X, eval_one]
    apply Subtype.ext
    change (smallIntegralInverse p 5).val*((4 : ℚ)+1)=1
    rw [smallIntegralInverse_value p 5 (by omega) (by omega)]
    norm_num
  have hsq : (comparisonCoordinateI p).eval
      ((v⁻¹ : (integralRationals p)ˣ) : integralRationals p)=
      smallIntegralInverse p 4 := by
    simp only [comparisonCoordinateI, eval_mul, eval_C, eval_add, eval_X, eval_one]
    apply Subtype.ext
    change (smallIntegralInverse p 5).val*((smallIntegralInverse p 4).val+1)=
      (smallIntegralInverse p 4).val
    rw [smallIntegralInverse_value p 5 (by omega) (by omega),
      smallIntegralInverse_value p 4 (by omega) (by omega)]
    norm_num
  have hfour : (4 : integralRationals p)*smallIntegralInverse p 4=1 :=
    (nativeFourUnitIntegral p hp).val_inv
  have hW4 : (movingEvenIntegral p).eval (v : integralRationals p)=
      (ActualJointGreen.finiteEvenSquaredIntegral p).eval 4-
        (ActualJointGreen.finiteEvenSquaredIntegral p).eval 1 := by
    simp only [movingEvenIntegral,eval_sub,eval_comp,eval_mul,eval_ofNat,hs4,mul_one]
  have hWq : (movingEvenIntegral p).eval
      ((v⁻¹ : (integralRationals p)ˣ) : integralRationals p)=
      (ActualJointGreen.finiteEvenSquaredIntegral p).eval 1-
        (ActualJointGreen.finiteEvenSquaredIntegral p).eval (smallIntegralInverse p 4) := by
    simp only [movingEvenIntegral,eval_sub,eval_comp,eval_mul,eval_ofNat,hsq,hfour]
  have hphase4 : LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) v
      (comparisonPhaseIntegral p)=
      17-4*((smallIntegralInverse p 4)^p+4^p) := by
    simp only [comparisonPhaseIntegral,map_sub,map_mul,map_ofNat,
      LaurentPolynomial.eval₂_T_n,LaurentPolynomial.eval₂_T_neg_n,
      hv,hvi]
    ring
  have hphaseq : LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) v⁻¹
      (comparisonPhaseIntegral p)=
      17-4*((smallIntegralInverse p 4)^p+4^p) := by
    rw [←native_inversion_eval]
    have hi : invert (comparisonPhaseIntegral p)=comparisonPhaseIntegral p := by
      simp only [comparisonPhaseIntegral,map_sub,map_mul,map_ofNat,invert_T,neg_neg]
      ring
    rw [hi,hphase4]
  change LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) v
      (comparisonIntegral p)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) v⁻¹
      (comparisonIntegral p)=0
  constructor
  · simp only [comparisonIntegral,map_add,map_mul,native_inversion_eval,
      LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,hW4,hWq,hphase4,comparisonEndIntegral]
    ring
  · simp only [comparisonIntegral,map_add,map_mul,native_inversion_eval,
      LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,LaurentPolynomial.eval₂_C,
      RingHom.id_apply,inv_inv,hW4,hWq,hphaseq,comparisonEndIntegral]
    ring

private theorem actual_zeta_zero_ends_integral (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp) (actualZetaIntegral p)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp)⁻¹ (actualZetaIntegral p)=0 := by
  have hA4 : (actualAbarIntegral p).eval (nativeFourUnitIntegral p hp : integralRationals p)=0 := by
    change (actualAbarIntegral p).eval (4 : integralRationals p)=0
    simp only [actualAbarIntegral,eval_mul,eval_sub,eval_ofNat,eval_X,
      sub_self,zero_mul]
  have hAq : (actualAbarIntegral p).eval
      (((nativeFourUnitIntegral p hp)⁻¹ : (integralRationals p)ˣ) :
        integralRationals p)=0 := by
    have hvi : (((nativeFourUnitIntegral p hp)⁻¹ : (integralRationals p)ˣ) :
        integralRationals p)=smallIntegralInverse p 4 := rfl
    have hfour : (4 : integralRationals p)*smallIntegralInverse p 4=1 :=
      (nativeFourUnitIntegral p hp).val_inv
    rw [hvi]
    simp only [actualAbarIntegral,eval_mul,eval_sub,eval_ofNat,eval_X,eval_one]
    rw [hfour,sub_self,mul_zero]
  have hp0 : p≠0 := (Fact.out : p.Prime).ne_zero
  constructor
  · simp only [actualZetaIntegral,map_mul,map_pow,LaurentPolynomial.eval₂_toLaurent,
      Polynomial.eval₂_id,hA4,zero_pow hp0,mul_zero]
  · simp only [actualZetaIntegral,map_mul,map_pow,LaurentPolynomial.eval₂_toLaurent,
      Polynomial.eval₂_id,hAq,zero_pow hp0,mul_zero]

/-- The original divided carrier has zero ends before reducing any coefficient. -/
theorem actual_balanced_zero_ends_integral (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp) (actualBalancedDividedIntegral p hp)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
      (nativeFourUnitIntegral p hp)⁻¹ (actualBalancedDividedIntegral p hp)=0 := by
  have hs := actual_comparison_zero_ends_integral p hp
  have hz := actual_zeta_zero_ends_integral p hp
  have hpI : (p : integralRationals p)≠0 := by
    intro he
    have hq : (p : ℚ)=0 := congrArg Subtype.val he
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hq
  have he4 := congrArg (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
    (nativeFourUnitIntegral p hp)) (actual_balanced_whole_p_source p hp)
  have heq := congrArg (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
    (nativeFourUnitIntegral p hp)⁻¹) (actual_balanced_whole_p_source p hp)
  simp only [actualBalancedNumeratorIntegral,map_add,map_mul,LaurentPolynomial.eval₂_C,
    RingHom.id_apply,hs.1,hs.2,hz.1,hz.2,zero_mul,mul_zero,add_zero] at he4 heq
  exact ⟨(mul_eq_zero.mp he4).resolve_left hpI,(mul_eq_zero.mp heq).resolve_left hpI⟩

/-- Both original endpoint conditions survive the genuine integral divided carrier. -/
theorem actual_balanced_zero_ends_field (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)
      (actualBalancedField p hp)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (ActualChiEndpoints.fourUnit p hp)⁻¹
      (actualBalancedField p hp)=0 := by
  have hu : Units.map (residueHom p).toMonoidHom (nativeFourUnitIntegral p hp)=
      ActualChiEndpoints.fourUnit p hp := by
    apply Units.ext
    change residueHom p (4 : integralRationals p)=4
    exact map_ofNat (residueHom p) 4
  have hs := actual_balanced_zero_ends_integral p hp
  have he4 := congrArg (residueHom p) hs.1
  have heq := congrArg (residueHom p) hs.2
  rw [native_eval₂_map,hu,map_zero,actualBalancedField_value] at he4
  rw [native_eval₂_map,map_inv,hu,map_zero,actualBalancedField_value] at heq
  exact ⟨he4,heq⟩

private theorem contract_degree_bound {R : Type*} [CommRing R]
    (P : R[X]) (n : ℕ) (hn : P.natDegree≤2*n) : (contract 2 P).natDegree≤n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_contract (by norm_num : (2 : ℕ)≠0)]
  apply coeff_eq_zero_of_natDegree_lt
  omega

/-- The characteristic-zero carrier degree is retained before division by p. -/
theorem actual_CB_degree_bound (hp : 19 ≤ p) :
    (greenCBq p hp).natDegree≤(p-1)/2+3*(p/6)-1 := by
  have hd : 0<p/6 := by omega
  have hB : (greenBq p hp).natDegree≤2*(p/6)-1 := by
    dsimp only [greenBq,greenBIntegral]
    apply natDegree_map_le.trans
    have hb := natDegree_mul_le_of_le (balancedFirstIntegral_degree p hp)
      (balancedProper_degree p hp)
    omega
  have hT : (WPFiniteCubicLog.Tc : ℚ[X]).natDegree≤3 := by
    unfold WPFiniteCubicLog.Tc
    compute_degree
  have hs : (greenCoordinateQ p).natDegree≤1 := by
    unfold greenCoordinateQ
    compute_degree
  have hcomp := natDegree_comp_le.trans (Nat.mul_le_mul hB hT)
  have hXp : (Polynomial.C (1/5 : ℚ)*X^p : ℚ[X]).natDegree≤p := by
    exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le p)
  have hprod := natDegree_mul_le_of_le hXp hcomp
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hbound : (Polynomial.C (1/5 : ℚ)*X^p*(greenBq p hp).comp WPFiniteCubicLog.Tc).natDegree≤
      2*((p-1)/2+3*(p/6)-1) := by omega
  have hcontract := contract_degree_bound _ _ hbound
  exact natDegree_comp_le.trans ((Nat.mul_le_mul hcontract hs).trans (by omega))

private theorem actual_even_squared_degree_Q (hp : 19 ≤ p) :
    ((ActualJointGreen.finiteEvenSquaredIntegral p).map (integralRationals p).subtype).natDegree≤
      (p-1)/2 := by
  rw [ActualJointGreen.finiteEvenSquaredIntegral,Polynomial.map_contract (by norm_num : (2 : ℕ)≠0),
    ActualJointGreen.finiteEvenLogIntegral_value p hp,ActualJointGreen.finiteEvenLogQ_eq_actual p hp]
  apply contract_degree_bound
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hh := rationalEvenLog_degree p
  omega

private theorem actual_moving_even_degree_Q (hp : 19 ≤ p) :
    ((movingEvenIntegral p).map (integralRationals p).subtype).natDegree≤(p-1)/2 := by
  simp only [movingEvenIntegral,Polynomial.map_sub,Polynomial.map_comp,
    Polynomial.map_mul,Polynomial.map_ofNat,comparisonCoordinateI,Polynomial.map_C,
    Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,
    Subring.subtype_apply,
    smallIntegralInverse_value p 5 (by omega) (by omega)]
  have hs : (Polynomial.C (1/5 : ℚ)*(X+1) : ℚ[X]).natDegree≤1 := by compute_degree
  have hs4 : (4*(Polynomial.C (1/5 : ℚ)*(X+1)) : ℚ[X]).natDegree≤1 := by compute_degree
  have hfirst : (((ActualJointGreen.finiteEvenSquaredIntegral p).map
      (integralRationals p).subtype).comp
        (4*(Polynomial.C (1/5 : ℚ)*(X+1)))).natDegree≤(p-1)/2 :=
    natDegree_comp_le.trans
      ((Nat.mul_le_mul (actual_even_squared_degree_Q p hp) hs4).trans (by omega))
  have hsecond : (((ActualJointGreen.finiteEvenSquaredIntegral p).map
      (integralRationals p).subtype).comp
        (Polynomial.C (1/5 : ℚ)*(X+1))).natDegree≤(p-1)/2 :=
    natDegree_comp_le.trans
      ((Nat.mul_le_mul (actual_even_squared_degree_Q p hp) hs).trans (by omega))
  simpa only [max_self,Nat.cast_ofNat] using natDegree_sub_le_of_le hfirst hsecond

private theorem actual_comparison_inversion_Q (hp : 19 ≤ p) :
    invert (comparisonRational p hp)=comparisonRational p hp := by
  unfold comparisonRational
  rw [←WPActualChiSource.coefficientMap_invert]
  congr 1
  simp only [comparisonIntegral,comparisonPhaseIntegral,map_add,map_mul,map_sub,map_ofNat,
    invert_C,invert_T,neg_neg,involutive_invert _]
  ring

private theorem actual_comparison_formula_Q (hp : 19≤p) :
    comparisonRational p hp=
      LaurentPolynomial.C (smallIntegralInverse p 15).val*
        (17-4*T (p : ℤ)-4*T (-(p : ℤ)))*
        (((movingEvenIntegral p).map (integralRationals p).subtype).toLaurent+
          invert ((movingEvenIntegral p).map (integralRationals p).subtype).toLaurent)+
      LaurentPolynomial.C
        ((smallIntegralInverse p 15*(17-4*((smallIntegralInverse p 4)^p+4^p))*
          comparisonEndIntegral p).val) := by
  have hphase : WPActualChiSource.coefficientMap (integralRationals p).subtype
      (comparisonPhaseIntegral p)=
      (17-4*T (p : ℤ)-4*T (-(p : ℤ)) : ℚ[T;T⁻¹]) := by
    simp only [comparisonPhaseIntegral,map_sub,map_mul,map_ofNat,
      WPActualChiSource.coefficientMap_T]
  rw [comparisonRational,comparisonIntegral,map_add,map_mul,map_mul,
    WPActualChiSource.coefficientMap_C,WPActualChiSource.coefficientMap_C]
  rw [map_add,WPActualChiSource.coefficientMap_toLaurent,
    WPActualChiSource.coefficientMap_invert,WPActualChiSource.coefficientMap_toLaurent,hphase]
  simp only [Subring.subtype_apply]

private theorem above_add_same {K : Type*} [Field K] (b : ℤ) (L M : K[T;T⁻¹])
    (hL : Above L b) (hM : Above M b) : Above (L+M) b := by
  simpa only [max_self] using Above_add hL hM

private theorem actual_comparison_above_Q (hp : 19 ≤ p) :
    Above (comparisonRational p hp) ((p : ℤ)+(((p-1)/2 : ℕ) : ℤ)) := by
  let n : ℤ := (((p-1)/2 : ℕ) : ℤ)
  let W := ((movingEvenIntegral p).map (integralRationals p).subtype).toLaurent
  have hW : Above W n := Above_toLaurent _ _ (actual_moving_even_degree_Q p hp)
  have hWi : Above (invert W) n :=
    Above_mono (Above_invert_toLaurent _) (by dsimp only [n]; omega)
  have hphase : Above (17-4*T (p : ℤ)-4*T (-(p : ℤ)) : ℚ[T;T⁻¹]) (p : ℤ) := by
    have h1 := Above_sub (Above_mono (b:=(p : ℤ)) (Above_C (17 : ℚ)) (by omega))
      (Above_monomial (4 : ℚ) (p : ℤ))
    have h2 := Above_sub (show Above (17-4*T (p : ℤ) : ℚ[T;T⁻¹]) (p : ℤ) by
      simpa only [max_self,map_ofNat] using h1)
      (Above_mono (b:=(p : ℤ)) (Above_monomial (4 : ℚ) (-(p : ℤ))) (by omega))
    simpa only [max_self,map_ofNat] using h2
  have hmain := Above_C_mul (Above_mul hphase (above_add_same n W (invert W) hW hWi))
    (smallIntegralInverse p 15).val
  have hbranch : Above (LaurentPolynomial.C
      ((smallIntegralInverse p 15*(17-4*((smallIntegralInverse p 4)^p+4^p))*
        comparisonEndIntegral p).val) : ℚ[T;T⁻¹]) ((p : ℤ)+n) :=
    Above_mono (Above_C _) (by dsimp only [n]; omega)
  have he := above_add_same ((p : ℤ)+n) _ _ hmain hbranch
  rw [actual_comparison_formula_Q p hp]
  simpa only [n,W,mul_assoc] using he

omit [Fact p.Prime] in
private theorem actual_zeta_above_Q (_hp : 19 ≤ p) : Above (zetaQ p) (p : ℤ) := by
  have hA : (WPFiniteZSource.Abar : ℚ[X]).natDegree≤2 := by
    unfold WPFiniteZSource.Abar
    compute_degree
  have hh := Above_C_mul (Above_mul (Above_monomial (1 : ℚ) (-(p : ℤ)))
    (Above_pow (Above_toLaurent _ _ hA) p))
    ((1/3 : ℚ)*(1/5 : ℚ)^(2*(p-1)))
  simpa only [zetaQ,map_one,one_mul,Nat.cast_ofNat,mul_assoc,
    show -(p : ℤ)+(p : ℤ)*2=p by omega] using hh

/-- Both literal support bounds of the actual rational divided numerator. -/
theorem actual_balanced_support_Q (hp : 19 ≤ p) :
    Above (actualBalancedDividedQ p hp) (4*(((p-1)/2 : ℕ) : ℤ)+1) ∧
      Above (invert (actualBalancedDividedQ p hp))
        (2*(((p-1)/2 : ℕ) : ℤ)+3*((p/6 : ℕ) : ℤ)+1) := by
  let n : ℤ := (((p-1)/2 : ℕ) : ℤ)
  let d : ℤ := ((p/6 : ℕ) : ℤ)
  have hhalf := WPFiniteWSource.half_exponent p hp
  have hdn : 3*d-1≤n := by dsimp only [n,d]; omega
  have hCB := Above_toLaurent (greenCBq p hp) _ (actual_CB_degree_bound p hp)
  have hCB' : Above (greenCBq p hp).toLaurent (n+3*d-1) := by
    convert hCB using 1
    dsimp only [n,d]
    omega
  have hCBe := Above_invert_toLaurent (greenCBq p hp)
  have hFdeg : ((squareQ p).comp WPActualPullbackSource.Vpolynomial).natDegree≤3*(p/6) := by
    have hV : (WPActualPullbackSource.Vpolynomial : ℚ[X]).natDegree≤3 := by
      unfold WPActualPullbackSource.Vpolynomial
      compute_degree
    exact natDegree_comp_le.trans ((Nat.mul_le_mul (actual_squareQ_degree p hp) hV).trans (by omega))
  have hF : Above (lowFpullQ p) (3*d) := by
    simpa only [lowFpullQ,Nat.cast_mul,Nat.cast_ofNat,d] using Above_toLaurent _ _ hFdeg
  have hFi : Above (invert (lowFpullQ p)) 0 := Above_invert_toLaurent _
  have hS := actual_comparison_above_Q p hp
  have hz := actual_zeta_above_Q p hp
  have hTn : Above (T n : ℚ[T;T⁻¹]) n := by
    simpa only [map_one,one_mul] using Above_monomial (1 : ℚ) n
  have hTneg : Above (T (-n) : ℚ[T;T⁻¹]) (-n) := by
    simpa only [map_one,one_mul] using Above_monomial (1 : ℚ) (-n)
  have htopG : Above (zetaQ p*(greenCBq p hp).toLaurent) (4*n+1) :=
    Above_mono (Above_mul hz hCB') (by dsimp only [n,d] at *; omega)
  have htopH : Above (zetaQ p*(T n*invert (greenCBq p hp).toLaurent)) (4*n+1) :=
    Above_mono (Above_mul hz (Above_mul hTn hCBe))
    (by dsimp only [n] at *; omega)
  have htopS : Above ((T n*invert (lowFpullQ p))*comparisonRational p hp) (4*n+1) :=
    Above_mono (Above_mul (Above_mul hTn hFi) hS)
    (by dsimp only [n] at *; omega)
  have htop := Above_C_mul (above_add_same (4*n+1) _ _
    (above_add_same (4*n+1) _ _ htopG htopH) htopS) (1/(p : ℚ))
  have hbotG : Above (zetaQ p*invert (greenCBq p hp).toLaurent) (2*n+3*d+1) :=
    Above_mono (Above_mul hz hCBe)
    (by dsimp only [n,d] at *; omega)
  have hbotH : Above (zetaQ p*(T (-n)*(greenCBq p hp).toLaurent)) (2*n+3*d+1) :=
    Above_mono (Above_mul hz (Above_mul hTneg hCB'))
    (by dsimp only [n,d] at *; omega)
  have hbotS : Above ((T (-n)*lowFpullQ p)*comparisonRational p hp) (2*n+3*d+1) :=
    Above_mono (Above_mul (Above_mul hTneg hF) hS)
    (by dsimp only [n,d] at *; omega)
  have hbot := Above_C_mul (above_add_same (2*n+3*d+1) _ _
    (above_add_same (2*n+3*d+1) _ _ hbotG hbotH) hbotS) (1/(p : ℚ))
  constructor
  · rw [actualBalancedDividedQ,actual_balanced_numerator_Q_source p hp]
    simpa only [mul_add,n] using htop
  · rw [actualBalancedDividedQ,actual_balanced_numerator_Q_source p hp]
    simpa only [
      map_mul,map_add,invert_C,invert_T,involutive_invert _,zeta_inversion_Q,
      actual_comparison_inversion_Q p hp,mul_add,n] using hbot

/-- The full actual support survives its integral quotient and field reduction. -/
theorem actual_balanced_support_field (hp : 19 ≤ p) (j : ℤ)
    (hj : j< -2*(((p-1)/2 : ℕ) : ℤ)-3*((p/6 : ℕ) : ℤ)-1 ∨
      4*(((p-1)/2 : ℕ) : ℤ)+1<j) :
    (actualBalancedField p hp).coeff j=0 := by
  have hs := actual_balanced_support_Q p hp
  have hq : (actualBalancedDividedQ p hp).coeff j=0 := by
    rcases hj with hj | hj
    · have he := hs.2 (-j) (by omega)
      simpa only [invert_apply,neg_neg] using he
    · exact hs.1 j hj
  have hi : (actualBalancedDividedIntegral p hp).coeff j=0 := by
    apply Subtype.ext
    change (integralRationals p).subtype ((actualBalancedDividedIntegral p hp).coeff j)=0
    rw [←WPActualChiSource.coefficientMap_coeff,actualBalancedDividedIntegral_value,hq]
  rw [actualBalancedField,WPActualChiSource.coefficientMap_coeff,hi,map_zero]

noncomputable def nativeBranchPhaseFirstIntegral : integralRationals p :=
  quotientI p 2*inverseTwoUnitI p*(inverseTwoUnitI p+1)-32*quotientI p 2-
    16*(p : integralRationals p)*(quotientI p 2)^2

theorem actual_branch_phase_first_source (hp : 19 ≤ p) :
    17-4*((smallIntegralInverse p 4)^p+(4 : integralRationals p)^p)=
      (p : integralRationals p)*nativeBranchPhaseFirstIntegral p := by
  have hc : (4 : integralRationals p)*smallIntegralInverse p 4=1 :=
    (nativeFourUnitIntegral p hp).val_inv
  obtain ⟨ha,hb,_⟩ := phase_end_power_sources p hp
  have hi := inverseTwoUnit_source p hp
  rw [ha,hb,twoUnit_source p hp]
  dsimp only [nativeBranchPhaseFirstIntegral]
  linear_combination -(inverseTwoUnitI p+1)*hi-(inverseTwoUnitI p)^2*hc

noncomputable def nativeComparisonBranchCarryIntegral : integralRationals p :=
  smallIntegralInverse p 15*nativeBranchPhaseFirstIntegral p*comparisonEndIntegral p

private theorem actual_even_squared_literal (hp : 19 ≤ p) :
    ActualJointGreen.finiteEvenSquaredIntegral p=
      ActualEntropyPolynomial.movingEvenIntegral p := by
  rw [ActualJointGreen.finiteEvenSquaredIntegral,
    ActualJointGreen.finiteEvenLogIntegral_eq_actual p hp,
    ActualEntropyLogAttachment.movingEvenIntegral_eq_actual_contract p hp]

/-- The actual rational branch first carry, before assigning a divided field value. -/
theorem actual_comparison_branch_first_source (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) (-1 : (integralRationals p)ˣ)
      (comparisonIntegral p)=(p : integralRationals p)*nativeComparisonBranchCarryIntegral p := by
  have hE0 : (ActualJointGreen.finiteEvenSquaredIntegral p).eval 0=0 := by
    rw [actual_even_squared_literal p hp]
    apply Subtype.ext
    change (integralRationals p).subtype
      ((ActualEntropyPolynomial.movingEvenIntegral p).eval 0)=0
    rw [←eval_map_apply,ActualEntropyPolynomial.movingEvenIntegral_value,
      map_zero,←coeff_zero_eq_eval_zero]
    simp only [ActualEntropyPolynomial.movingEvenQ,
      WPActualRankTwoLegendreField.rankCoefficientPolynomial_coeff,
      Nat.zero_lt_succ,ite_true]
  have hW0 : (movingEvenIntegral p).eval (-1 : integralRationals p)=0 := by
    simp only [movingEvenIntegral,eval_sub,eval_comp,eval_mul,eval_ofNat,
      comparisonCoordinateI,eval_add,eval_X,eval_one,neg_add_cancel,mul_zero,hE0,sub_self]
  have hminus : (-1 : (integralRationals p)ˣ)⁻¹=(-1 : (integralRationals p)ˣ) := by
    apply Units.ext
    rfl
  simp only [comparisonIntegral,map_add,map_mul,native_inversion_eval,
    hminus,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,
    Units.val_neg,Units.val_one,hW0,zero_add,mul_zero,
    LaurentPolynomial.eval₂_C,RingHom.id_apply]
  rw [actual_branch_phase_first_source p hp]
  dsimp only [nativeComparisonBranchCarryIntegral]
  ring

/-- The branch scalar is obtained from the literal phase quotient and even endpoints. -/
theorem actual_comparison_branch_carry_field (hp : 19 ≤ p) :
    residueHom p (nativeComparisonBranchCarryIntegral p)=
      -2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
        (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
          (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p) := by
  have hEnd : comparisonEndIntegral p=ActualWeightedF0Carry.DendI p := by
    rw [comparisonEndIntegral,actual_even_squared_literal p hp,ActualWeightedF0Carry.DendI]
  simp only [nativeComparisonBranchCarryIntegral,nativeBranchPhaseFirstIntegral,
    map_mul,map_add,map_sub,map_pow,map_natCast,map_ofNat,map_one,quotientI,map_intCast,
    ZMod.natCast_self,inverseTwoUnitI_field p hp,
    smallIntegralInverse_field p 15 (by omega) (by omega),hEnd,
    ActualWeightedF0Carry.DendI_field p hp]
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have h15 : (15 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 15 (by omega) (by omega)
  field_simp [h2,h4,h15]
  ring

/-- The actual conic proper carrier vanishes to at least second order at the branch. -/
theorem actual_CB_branch_zero_jets (hp : 19 ≤ p) :
    (actualCBIntegral p hp).eval (-1)=0 ∧ (actualCBIntegral p hp).derivative.eval (-1)=0 := by
  let P : (integralRationals p)[X] := contract 2
    (Polynomial.C (smallIntegralInverse p 5)*X^p*(greenBIntegral p hp).comp (cubicTIntegral p))
  have hc (k : ℕ) (hk : k≤1) : P.coeff k=0 := by
    dsimp only [P]
    rw [coeff_contract (by norm_num : (2 : ℕ)≠0),mul_assoc,coeff_C_mul,
      coeff_X_pow_mul',if_neg (by omega : ¬p≤k*2),mul_zero]
  have hs : (comparisonCoordinateI p).eval (-1)=0 := by
    simp only [comparisonCoordinateI,eval_mul,eval_C,eval_add,eval_X,eval_one,
      neg_add_cancel,mul_zero]
  have h0 : P.eval 0=0 := by rw [←coeff_zero_eq_eval_zero,hc 0 (by omega)]
  have h1 : P.derivative.eval 0=0 := by
    rw [←coeff_zero_eq_eval_zero,coeff_derivative]
    simp only [Nat.zero_add,hc 1 (by omega),zero_mul]
  constructor
  · change (P.comp (comparisonCoordinateI p)).eval (-1)=0
    rw [eval_comp,hs,h0]
  · change ((P.comp (comparisonCoordinateI p)).derivative).eval (-1)=0
    rw [derivative_comp,eval_mul,eval_comp,hs,h1,mul_zero]

private theorem actual_proper_branch_jets_Q (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (nativeProperGQ p hp)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (nativeProperHQ p hp)=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (nativeProperGQ p hp))=0 ∧
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (nativeProperHQ p hp))=0 := by
  have hi := actual_CB_branch_zero_jets p hp
  have h0 := congrArg (integralRationals p).subtype hi.1
  have h1 := congrArg (integralRationals p).subtype hi.2
  simp only [←eval_map_apply,actual_CB_rational_value p hp,map_neg,map_one,map_zero] at h0
  simp only [←eval_map_apply,←Polynomial.derivative_map,actual_CB_rational_value p hp,
    map_neg,map_one,map_zero] at h1
  have hG : LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (nativeProperGQ p hp)=0 := by
    simp only [nativeProperGQ,map_mul,LaurentPolynomial.eval₂_toLaurent,
      Polynomial.eval₂_id,Units.val_neg,Units.val_one,h0,mul_zero]
  have hdG : LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (nativeProperGQ p hp))=0 := by
    simp only [nativeProperGQ,D_mul,map_add,map_mul,D_toLaurent,
      LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_id,Units.val_neg,Units.val_one,
      h0,h1,mul_zero,add_zero]
  refine ⟨hG,?_,hdG,?_⟩
  · simp only [nativeProperHQ,map_mul,native_inversion_eval,inv_neg,inv_one,hG,mul_zero]
  · simp only [nativeProperHQ,D_mul,map_add,map_mul,D_invert,map_neg,
      native_inversion_eval,inv_neg,inv_one,hG,hdG,mul_zero,neg_zero,add_zero]

private theorem actual_comparison_branch_derivative_Q (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (comparisonRational p hp))=0 := by
  have he := congrArg D (actual_comparison_inversion_Q p hp)
  rw [D_invert] at he
  have hv := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ)) he
  simp only [map_neg,map_mul,native_inversion_eval,inv_neg,inv_one] at hv
  norm_num at hv
  linear_combination -(1/2 : ℚ)*hv

private theorem minus_unit_subtype :
    Units.map (integralRationals p).subtype.toMonoidHom (-1 : (integralRationals p)ˣ)=
      (-1 : ℚˣ) := by
  apply Units.ext
  change (integralRationals p).subtype (-1 : integralRationals p)=(-1 : ℚ)
  rw [map_neg,map_one]

private theorem actual_comparison_branch_Q (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (comparisonRational p hp)=
      (p : ℚ)*(nativeComparisonBranchCarryIntegral p).val := by
  have he := congrArg (integralRationals p).subtype (actual_comparison_branch_first_source p hp)
  rw [native_eval₂_map,minus_unit_subtype] at he
  simpa only [comparisonRational,map_mul,map_natCast,Subring.subtype_apply] using he

/-- Both branch jets come from the characteristic-zero divided numerator.
The odd-degree case retains its derivative jet even when f(-1)=0. -/
theorem actual_balanced_branch_jets_Q (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (actualBalancedDividedQ p hp)=
      LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (actualLowMQ p hp)*
        (nativeComparisonBranchCarryIntegral p).val ∧
    LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (actualBalancedDividedQ p hp))=
      LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ) (D (actualLowMQ p hp))*
        (nativeComparisonBranchCarryIntegral p).val := by
  have hpq : (p : ℚ)≠0 := by positivity
  have hj := actual_proper_branch_jets_Q p hp
  have hwhole : LaurentPolynomial.C (p : ℚ)*actualBalancedDividedQ p hp=
      nativeProperGQ p hp+nativeProperHQ p hp+actualLowMQ p hp*comparisonRational p hp := by
    have he := actual_balanced_whole_p_source_Q p hp
    rw [actual_balanced_numeratorQ_factor p hp,actual_proper_sum_Q p hp] at he
    exact he
  have h0 := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ)) hwhole
  have hd := congrArg D hwhole
  rw [D_C_mul] at hd
  simp only [map_add,D_mul] at hd
  have h1 := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℚ) (-1 : ℚˣ)) hd
  simp only [map_add,map_mul,LaurentPolynomial.eval₂_C,RingHom.id_apply,
    hj.1,hj.2.1,zero_add,actual_comparison_branch_Q p hp] at h0
  simp only [map_add,map_mul,LaurentPolynomial.eval₂_C,RingHom.id_apply,
    hj.2.2.1,hj.2.2.2,zero_add,actual_comparison_branch_Q p hp,
    actual_comparison_branch_derivative_Q p hp,mul_zero,add_zero] at h1
  constructor
  · apply mul_left_cancel₀ hpq
    linear_combination h0
  · apply mul_left_cancel₀ hpq
    linear_combination h1

/-- The exact integral branch value and derivative normalize the actual quotient. -/
theorem actual_balanced_branch_jets_integral (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) (-1 : (integralRationals p)ˣ)
      (actualBalancedDividedIntegral p hp)=
      LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) (-1 : (integralRationals p)ˣ)
        (actualLowMIntegral p hp)*nativeComparisonBranchCarryIntegral p ∧
    LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) (-1 : (integralRationals p)ˣ)
      (nativeRingD (actualBalancedDividedIntegral p hp))=
      LaurentPolynomial.eval₂ (RingHom.id (integralRationals p)) (-1 : (integralRationals p)ˣ)
        (nativeRingD (actualLowMIntegral p hp))*nativeComparisonBranchCarryIntegral p := by
  have hq := actual_balanced_branch_jets_Q p hp
  constructor <;> apply Subtype.ext
  · change (integralRationals p).subtype
        (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
          (-1 : (integralRationals p)ˣ) (actualBalancedDividedIntegral p hp))=
      (integralRationals p).subtype
        (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
          (-1 : (integralRationals p)ˣ) (actualLowMIntegral p hp)*
            nativeComparisonBranchCarryIntegral p)
    rw [map_mul,native_eval₂_map,native_eval₂_map,minus_unit_subtype,
      actualBalancedDividedIntegral_value,actualLowMQ_value]
    simpa only [Subring.subtype_apply] using hq.1
  · change (integralRationals p).subtype
        (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
          (-1 : (integralRationals p)ˣ) (nativeRingD (actualBalancedDividedIntegral p hp)))=
      (integralRationals p).subtype
        (LaurentPolynomial.eval₂ (RingHom.id (integralRationals p))
          (-1 : (integralRationals p)ˣ) (nativeRingD (actualLowMIntegral p hp))*
            nativeComparisonBranchCarryIntegral p)
    rw [map_mul,native_eval₂_map,native_eval₂_map,minus_unit_subtype,
      integral_derivative_map,integral_derivative_map,
      actualBalancedDividedIntegral_value,actualLowMQ_value]
    simpa only [Subring.subtype_apply] using hq.2

/-- The original branch normalization keeps the odd first jet after reduction. -/
theorem actual_balanced_branch_jets_field (hp : 19 ≤ p) :
    let f := (NativeChiFieldSource.halfPullbackField p hp).toLaurent
    let b := -2*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)^2-
      (3/2 : ZMod p)*(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p)*
        (WPFiniteInversion.integerFermatQuotient p 3 : ZMod p)
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (actualBalancedField p hp)=
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) f*b ∧
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (D (actualBalancedField p hp))=
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (-1 : (ZMod p)ˣ) (D f)*b := by
  have hu : Units.map (residueHom p).toMonoidHom (-1 : (integralRationals p)ˣ)=
      (-1 : (ZMod p)ˣ) := by
    apply Units.ext
    change residueHom p (-1 : integralRationals p)=(-1 : ZMod p)
    rw [map_neg,map_one]
  have hi := actual_balanced_branch_jets_integral p hp
  have h0 := congrArg (residueHom p) hi.1
  have h1 := congrArg (residueHom p) hi.2
  simp only [native_eval₂_map,hu,map_mul,actual_comparison_branch_carry_field p hp,
    actual_low_multiplier_field p hp,actualLowFIntegral_field p hp,
    integral_derivative_map,actualBalancedField_value] at h0 h1
  exact ⟨h0,h1⟩

omit [Fact p.Prime] in
private theorem legendre_branch_jet_nontrivial {K : Type*} [Field K] [CharP K p]
    (d : ℕ) (Y : K[X]) (hdegree : Y.natDegree<p) (hY : Y≠0)
    (hODE : WPActualRankTwoGaussODE.legendreJacobi d Y=0) :
    Y.eval 0≠0 ∨ Y.derivative.eval 0≠0 := by
  classical
  by_contra hn
  have hzero : Y.coeff 0=0 := by
    rw [coeff_zero_eq_eval_zero]
    exact not_ne_iff.mp (fun h => hn (Or.inl h))
  have hone : Y.coeff 1=0 := by
    have he : Y.derivative.eval 0=0 := not_ne_iff.mp (fun h => hn (Or.inr h))
    rw [←coeff_zero_eq_eval_zero,coeff_derivative] at he
    simpa only [Nat.cast_zero,zero_add,mul_one] using he
  have hex : ∃ n : ℕ, Y.coeff n≠0 := by
    by_contra he
    apply hY
    ext n
    exact not_ne_iff.mp (fun hc => he ⟨n,hc⟩)
  let n := Nat.find hex
  have hc : Y.coeff n≠0 := Nat.find_spec hex
  have hmin (j : ℕ) (hj : j<n) : Y.coeff j=0 := by
    by_contra he
    have hle := Nat.find_min' hex he
    dsimp only [n] at hj
    omega
  have hn2 : 2≤n := by
    by_contra he
    have hn01 : n=0 ∨ n=1 := by omega
    rcases hn01 with he | he
    · apply hc
      simpa only [he] using hzero
    · apply hc
      simpa only [he] using hone
  have hnp : n<p := by
    by_contra he
    exact hc (coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (by omega)))
  have hlow := hmin (n-2) (by omega)
  have hx1 : (X*Y.derivative).coeff (n-2)=0 := by
    rw [←pow_one X,coeff_X_pow_mul']
    by_cases he : 3≤n
    · rw [if_pos (by omega),coeff_derivative,
        show n-2-1+1=n-2 by omega,hlow,zero_mul]
    · rw [if_neg (by omega)]
  have hx2 : (X^2*Y.derivative.derivative).coeff (n-2)=0 := by
    rw [coeff_X_pow_mul']
    by_cases he : 4≤n
    · rw [if_pos (by omega),coeff_derivative,coeff_derivative,
        show n-2-2+1+1=n-2 by omega,hlow,zero_mul,zero_mul]
    · rw [if_neg (by omega)]
  have hdd : Y.derivative.derivative.coeff (n-2)=
      Y.coeff n*(n : K)*((n-1 : ℕ) : K) := by
    have hcastn : ((n-1 : ℕ) : K)+1=(n : K) := by
      have he := congrArg (fun j : ℕ => (j : K)) (show n-1+1=n by omega)
      simpa only [Nat.cast_add,Nat.cast_one] using he
    have hcastpred : ((n-2 : ℕ) : K)+1=((n-1 : ℕ) : K) := by
      have he := congrArg (fun j : ℕ => (j : K)) (show n-2+1=n-1 by omega)
      simpa only [Nat.cast_add,Nat.cast_one] using he
    rw [coeff_derivative,coeff_derivative,
      show n-2+1+1=n by omega,show n-2+1=n-1 by omega,hcastn,hcastpred]
  have he := congrArg (fun P : K[X] => P.coeff (n-2)) hODE
  have hwhole : WPActualRankTwoGaussODE.legendreJacobi d Y=
      Y.derivative.derivative-X^2*Y.derivative.derivative-
        Polynomial.C (2 : K)*(X*Y.derivative)+Polynomial.C ((d : K)*((d : K)+1))*Y := by
    simp only [WPActualRankTwoGaussODE.legendreJacobi,sub_mul,one_mul,C_ofNat]
    ring
  rw [hwhole] at he
  simp only [coeff_add,coeff_sub,coeff_C_mul,hx1,hx2,hlow,hdd,
    coeff_zero,mul_zero,sub_zero,add_zero] at he
  have hnc : (n : K)≠0 := WPFiniteField.denominator_ne_zero p n
    (Finset.mem_Ico.mpr (by omega))
  have hn1c : ((n-1 : ℕ) : K)≠0 := WPFiniteField.denominator_ne_zero p (n-1)
    (Finset.mem_Ico.mpr (by omega))
  exact (mul_ne_zero (mul_ne_zero hc hnc) hn1c) he

/-- The actual normalized low Jacobi polynomial cannot lose both branch jets. -/
theorem actual_low_Jacobi_branch_nontrivial (hp : 19≤p) :
    (WPActualRankTwoLegendreField.actualLegendreJacobi p).eval 0≠0 ∨
      (WPActualRankTwoLegendreField.actualLegendreJacobi p).derivative.eval 0≠0 := by
  let Y := WPActualRankTwoLegendreField.actualLegendreJacobi p
  have hODE : WPActualRankTwoGaussODE.legendreJacobi (p/6) Y=0 :=
    WPActualRankTwoComparison.actualLegendreJacobi_source_zero p (by omega)
  have hdegree : Y.natDegree<p := by
    exact (WPActualRankTwoComparison.actualLegendreJacobi_degree p).trans_lt (by omega)
  have hYone : Y.eval 1=1 := WPActualRankTwoComparison.actualLegendreJacobi_endpoint_one p
  have hY : Y≠0 := by
    intro hz
    rw [hz,eval_zero] at hYone
    exact zero_ne_one hYone
  exact legendre_branch_jet_nontrivial p (p/6) Y hdegree hY hODE

private theorem actual_low_F_conic_Q (hp : 19≤p) :
    (((squareQ p).comp WPActualPullbackSource.Vpolynomial).comp (5*X^2-1))=
      ((WPActualRankTwoParameter.rankJacobiNode p 1).comp (4*X^3-3*X))^2 := by
  let Y := WPActualRankTwoParameter.rankJacobiNode p 1
  have hYe : Y.comp (-X)=Polynomial.C ((-1 : ℚ)^(p/6))*Y := by
    have he := congrArg (Polynomial.map (integralRationals p).subtype)
      (greenBalancedFirst_reflect p hp)
    simpa only [Polynomial.map_comp,Polynomial.map_neg,Polynomial.map_X,
      Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_one,
      map_pow,map_neg,map_one,
      balancedFirstIntegral_value,Y] using he
  have hFe : (Y^2).comp (-X)=Y^2 := by
    simp only [pow_comp,hYe,mul_pow,←Polynomial.C_pow,sign_square,Polynomial.C_1,one_mul]
  have hq : (squareQ p).comp (1-X^2)=Y^2 :=
    quadraticInverse_even_pullback (Y^2) (by norm_num) hFe
  have hV : WPActualPullbackSource.Vpolynomial.comp (5*X^2-1)=1-(4*X^3-3*X)^2 := by
    have h125 : (125 : ℚ[X])*Polynomial.C (1/125 : ℚ)=1 := by
      change Polynomial.C (125 : ℚ)*Polynomial.C (1/125 : ℚ)=Polynomial.C 1
      rw [←Polynomial.C_mul]
      norm_num
    simp only [WPActualPullbackSource.Vpolynomial,mul_comp,sub_comp,ofNat_comp,
      C_comp,one_comp,pow_comp,X_comp]
    linear_combination (1-(4*X^3-3*X)^2)*h125
  rw [comp_assoc,hV,
    show 1-(4*X^3-3*X)^2=(1-X^2 : ℚ[X]).comp (4*X^3-3*X) by
      simp only [sub_comp,one_comp,pow_comp,X_comp],←comp_assoc,hq,pow_comp]

/-- The actual low multiplier is attached to its original cubic conic square. -/
theorem actual_low_F_conic_field (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).comp (5*X^2-1)=
      ((WPActualRankTwoLegendreField.actualLegendreJacobi p).comp (4*X^3-3*X))^2 := by
  let FI := (squareQIntegral p hp).comp (WPHasseIntegralTransport.integralV p (by omega))
  let YI := WPActualRankTwoLegendreField.rankIntegralJacobi p (by omega) 1
  have hI : FI.comp (5*X^2-1)=(YI.comp (4*X^3-3*X))^2 := by
    apply Polynomial.map_injective (integralRationals p).subtype Subtype.val_injective
    simp only [FI,YI,Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_mul,
      Polynomial.map_pow,Polynomial.map_X,Polynomial.map_ofNat,
      Polynomial.map_one,
      squareQIntegral_value p hp,WPHasseIntegralTransport.integralV_map_rational,
      WPActualRankTwoLegendreField.rankIntegralJacobi_value]
    exact actual_low_F_conic_Q p hp
  have hf : FI.map (residueHom p)=NativeChiFieldSource.halfPullbackField p hp := by
    ext n
    have he := congrArg (fun L : (ZMod p)[T;T⁻¹] => L.coeff (n : ℤ))
      (actualLowFIntegral_field p hp)
    simpa only [actualLowFIntegral,WPActualChiSource.coefficientMap_toLaurent,
      WPFiniteJCarrier.toLaurent_coeff_nat,FI] using he
  have he := congrArg (Polynomial.map (residueHom p)) hI
  simpa only [Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,Polynomial.map_ofNat,hf,YI,
    Polynomial.map_one,
    WPActualRankTwoLegendreField.rankIntegralJacobi_field] using he

private theorem conic_square_branch_jets {K : Type*} [Field K]
    (h2 : (2 : K)≠0) (h5 : (5 : K)≠0) (F Y : K[X])
    (hconic : F.comp (5*X^2-1)=(Y.comp (4*X^3-3*X))^2) :
    F.eval (-1)=Y.eval 0^2 ∧
      (Y.eval 0=0 → F.derivative.eval (-1)=(9/5 : K)*Y.derivative.eval 0^2) := by
  have hzero := congrArg (fun P : K[X] => P.eval 0) hconic
  simp only [eval_comp,eval_sub,eval_mul,eval_pow,eval_X,eval_ofNat,
    eval_one,
    zero_pow (by norm_num : (2 : ℕ)≠0),zero_pow (by norm_num : (3 : ℕ)≠0),
    mul_zero,zero_sub,sub_zero] at hzero
  refine ⟨hzero,?_⟩
  intro hy
  have hchain (P Q : K[X]) :
      (P.comp Q).derivative.derivative.eval 0=
        P.derivative.derivative.eval (Q.eval 0)*Q.derivative.eval 0^2+
          P.derivative.eval (Q.eval 0)*Q.derivative.derivative.eval 0 := by
    rw [derivative_comp,derivative_mul,derivative_comp]
    simp only [eval_add,eval_mul,eval_comp]
    ring
  have hsquare (P : K[X]) : (P^2).derivative.derivative.eval 0=
      2*P.derivative.eval 0^2+2*P.eval 0*P.derivative.derivative.eval 0 := by
    rw [derivative_sq,derivative_mul,derivative_mul]
    simp only [derivative_C,zero_mul,zero_add,eval_add,eval_mul,eval_C]
    ring
  have he := congrArg (fun P : K[X] => P.derivative.derivative.eval 0) hconic
  rw [hchain,hsquare,derivative_comp] at he
  norm_num [derivative_sub,derivative_mul,derivative_pow,derivative_X,
    derivative_ofNat,derivative_one,eval_comp,hy] at he
  have hten : (10 : K)≠0 := by
    rw [show (10 : K)=2*5 by ring]
    exact mul_ne_zero h2 h5
  have hnum : (10 : K)*(9/5)=18 := by
    rw [←mul_div_assoc]
    apply (div_eq_iff h5).2
    ring
  have hsource : (10 : K)*F.derivative.eval (-1)=18*Y.derivative.eval 0^2 := by
    linear_combination he
  apply mul_left_cancel₀ hten
  rw [hsource]
  linear_combination -Y.derivative.eval 0^2*hnum

/-- The actual branch multiplier has a value or a first jet, including the odd CM class. -/
theorem actual_balanced_branch_multiplier_nontrivial_field (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).eval (-1)≠0 ∨
      (NativeChiFieldSource.halfPullbackField p hp).derivative.eval (-1)≠0 := by
  have h2 : (2 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)
  have hj := conic_square_branch_jets h2 h5
    (NativeChiFieldSource.halfPullbackField p hp)
    (WPActualRankTwoLegendreField.actualLegendreJacobi p) (actual_low_F_conic_field p hp)
  by_cases hY0 : (WPActualRankTwoLegendreField.actualLegendreJacobi p).eval 0=0
  · have hY1 := (actual_low_Jacobi_branch_nontrivial p hp).resolve_left (not_ne_iff.mpr hY0)
    right
    rw [hj.2 hY0]
    have h9 : (9 : ZMod p)≠0 := by
      rw [show (9 : ZMod p)=3^2 by ring]
      exact pow_ne_zero _ h3
    exact mul_ne_zero (div_ne_zero h9 h5) (pow_ne_zero _ hY1)
  · left
    rw [hj.1]
    exact pow_ne_zero _ hY0

private theorem conic_square_rootMultiplicity_le_two {K : Type*} [Field K] [IsAlgClosed K]
    (h2 : (2 : K)≠0) (h3 : (3 : K)≠0) (h5 : (5 : K)≠0) (F Y n : K[X])
    (hconic : F.comp (5*X^2-1)=(Y.comp (4*X^3-3*X))^2)
    (hmetric : (1-X^2)*(Y*n.derivative-Y.derivative*n)=1-Y^2) (a : K) :
    F.rootMultiplicity a≤2 := by
  by_contra hn
  have h0 := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p:=F) (t:=a) (n:=0) (by omega)
  have h1 := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p:=F) (t:=a) (n:=1) (by omega)
  have h2jet := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
    (p:=F) (t:=a) (n:=2) (by omega)
  change F.eval a=0 at h0
  change F.derivative.eval a=0 at h1
  change F.derivative.derivative.eval a=0 at h2jet
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq ((a+1)/5) (by decide : 0<(2 : ℕ))
  let Q : K[X] := 5*X^2-1
  let Tc : K[X] := 4*X^3-3*X
  let v : K := Tc.eval t
  have hqt : Q.eval t=a := by
    simp only [Q,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one,ht]
    rw [mul_div_cancel₀ _ h5]
    ring
  have hval := congrArg (fun P : K[X] => P.eval t) hconic
  change (F.comp Q).eval t=((Y.comp Tc)^2).eval t at hval
  rw [eval_comp,hqt,h0,eval_pow,eval_comp] at hval
  have hyv : Y.eval v=0 := by
    exact eq_zero_of_pow_eq_zero hval.symm
  have hw := congrArg (fun P : K[X] => P.eval v) hmetric
  simp only [eval_mul,eval_sub,eval_pow,eval_one,eval_X,hyv,zero_mul,zero_pow
    (by norm_num : (2 : ℕ)≠0),sub_zero,zero_sub] at hw
  have hyd : Y.derivative.eval v≠0 := by
    intro hz
    rw [hz,zero_mul,neg_zero,mul_zero] at hw
    exact zero_ne_one hw
  have hqv : 1-v^2≠0 := by
    intro hz
    rw [hz,zero_mul] at hw
    exact zero_ne_one hw
  have hgeom : 1-v^2=(1-t^2)*(4*t^2-1)^2 := by
    simp only [v,Tc,eval_sub,eval_mul,eval_ofNat,eval_pow,eval_X]
    ring
  have htc : Tc.derivative.eval t=3*(4*t^2-1) := by
    norm_num [Tc,derivative_sub,derivative_mul,derivative_pow]
    ring
  have htd : Tc.derivative.eval t≠0 := by
    intro hz
    rw [htc] at hz
    have hz' := (mul_eq_zero.mp hz).resolve_left h3
    apply hqv
    rw [hgeom,hz',zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]
  have hchain (P R : K[X]) :
      (P.comp R).derivative.derivative.eval t=
        P.derivative.derivative.eval (R.eval t)*R.derivative.eval t^2+
          P.derivative.eval (R.eval t)*R.derivative.derivative.eval t := by
    rw [derivative_comp,derivative_mul,derivative_comp]
    simp only [eval_add,eval_mul,eval_comp]
    ring
  have hsquare (P : K[X]) : (P^2).derivative.derivative.eval t=
      2*P.derivative.eval t^2+2*P.eval t*P.derivative.derivative.eval t := by
    rw [derivative_sq,derivative_mul,derivative_mul]
    simp only [derivative_C,zero_mul,zero_add,eval_add,eval_mul,eval_C]
    ring
  have hd := congrArg (fun P : K[X] => P.derivative.derivative.eval t) hconic
  change (F.comp Q).derivative.derivative.eval t=
    ((Y.comp Tc)^2).derivative.derivative.eval t at hd
  rw [hchain,hsquare,derivative_comp] at hd
  have hyv' : Y.eval (Tc.eval t)=0 := hyv
  simp only [eval_comp,eval_mul,hqt,h1,h2jet,hyv',zero_mul,mul_zero,add_zero] at hd
  change (0 : K)=2*(Tc.derivative.eval t*Y.derivative.eval v)^2 at hd
  exact (mul_ne_zero h2 (pow_ne_zero 2 (mul_ne_zero htd hyd))) hd.symm

/-- Every actual multiplier root retains multiplicity at most two in an algebraic closure.
The original proper Jacobi metric prevents a hidden repeated period root. -/
theorem actual_balanced_multiplier_rootMultiplicity_le_two {K : Type*}
    [Field K] [CharP K p] [IsAlgClosed K] (hp : 19≤p) (a : K) :
    ((NativeChiFieldSource.halfPullbackField p hp).map
      (ActualThreePhase.φ (K:=K) p)).rootMultiplicity a≤2 := by
  let φ : ZMod p →+* K := ActualThreePhase.φ p
  let F := (NativeChiFieldSource.halfPullbackField p hp).map φ
  let Y := (WPActualRankTwoLegendreField.actualLegendreJacobi p).map φ
  let n := (WPActualRankTwoProper.properLegendreJacobi p).map φ
  have hc := congrArg (Polynomial.map φ) (actual_low_F_conic_field p hp)
  simp only [Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_mul,
    Polynomial.map_pow,Polynomial.map_X,Polynomial.map_ofNat,Polynomial.map_one] at hc
  have hm := congrArg (Polynomial.map φ)
    (WPActualRankTwoProper.properLegendreJacobi_wronskian p (by omega))
  simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow,
    Polynomial.map_X,Polynomial.map_one,←Polynomial.derivative_map] at hm
  have h2 : (2 : K)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  exact conic_square_rootMultiplicity_le_two h2 h3 h5 F Y n hc hm a

/-- The original low multiplier retains its full leading degree after reduction. -/
theorem actual_balanced_multiplier_exact_degree (hp : 19≤p) :
    (NativeChiFieldSource.halfPullbackField p hp).natDegree=3*(p/6) := by
  have h5 : (5 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 5
    (by omega) (by omega)
  have h4 : (4 : ZMod p)≠0 := WPActualGaussProper.small_cast_ne_zero p 4
    (by omega) (by omega)
  have hq : (5*X^2-1 : (ZMod p)[X]).natDegree=2 := by
    compute_degree
    exact h5
  have ht : (4*X^3-3*X : (ZMod p)[X]).natDegree=3 := by
    compute_degree
    exact h4
    norm_num
  have he := congrArg Polynomial.natDegree (actual_low_F_conic_field p hp)
  rw [natDegree_comp,hq,natDegree_pow,natDegree_comp,ht,
    WPActualNativeDegree.actualLegendreJacobi_exact_degree p hp] at he
  omega

end WPFieldAssembly.SourceClosureBalancedFirstSource
