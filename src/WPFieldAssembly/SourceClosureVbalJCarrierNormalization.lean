import WPFieldAssembly.SourceClosureVbalFrobeniusNormalization
import Mathlib.Algebra.Polynomial.Expand

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteWSource WPFiniteJSource
  WPFiniteJHighCoefficient WPFiniteKSource WPFiniteJCarrier WPFiniteZSource
  WPFiniteCubicLog

namespace WPFieldAssembly.SourceClosureVbalJCarrierNormalization

variable {K : Type*} [Field K]

set_option maxHeartbeats 1600000

/-- The actual conic contraction of the complete J_L primitive is its full HJP row. -/
theorem actual_native_J_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (contract 2 (Polynomial.C (1/5 : K)*X^p*(JLP p).comp Tc)).comp
      squaredCoordinate=Polynomial.C (1/5 : K)*HJP p := by
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hunit : (Polynomial.C (5 : K)*Polynomial.C ((5 : K)⁻¹) : K[X])=1 := by
    rw [←Polynomial.C_mul,mul_inv_cancel₀ h5,Polynomial.C_1]
  have hlinear : ((5*X-1 : K[X]).comp squaredCoordinate)=X := by
    simp only [sub_comp,mul_comp,ofNat_comp,X_comp,one_comp,squaredCoordinate]
    change Polynomial.C (5 : K)*(Polynomial.C ((5 : K)⁻¹)*(X+1))-1=X
    linear_combination (X+1)*hunit
  have hconic : (5*X-1 : K[X]).comp (X^2)=conic := by
    norm_num [sub_comp,mul_comp,ofNat_comp,X_comp,one_comp,conic]
  have hraw : (Polynomial.C (1/5 : K)*X^p*(JLP p).comp Tc : K[X])=
      ((Polynomial.C (1/5 : K)*HJP p).comp (5*X-1)).comp (X^2) := by
    rw [comp_assoc,hconic,mul_comp,C_comp,HJP_conic_pullback p hp]
    ring
  rw [hraw,←expand_eq_comp_X_pow,contract_expand 2 (by decide : (2 : ℕ)≠0),
    comp_assoc,hlinear,comp_X]

private theorem original_zeta_phase (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    (LaurentPolynomial.C (1/3 : K)*T (-(p : ℤ))*(Abar : K[X]).toLaurent^p)=
      LaurentPolynomial.C (1/3 : K)*phase p := by
  have ht : (T (-(p : ℤ))*T (p : ℤ) : K[T;T⁻¹])=1 := by
    rw [←T_add,neg_add_cancel,T_zero]
  rw [phase_factorization p hp]
  linear_combination LaurentPolynomial.C (1/3 : K)*phase p*ht

/-- Both actual proper J halves retain exactly three copies of the original GJ carrier. -/
theorem actual_native_J_pair (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    let zeta : K[T;T⁻¹] := LaurentPolynomial.C (1/3 : K)*T (-(p : ℤ))*
      (Abar : K[X]).toLaurent^p
    let J := (Polynomial.C (1/5 : K)*HJP p).toLaurent
    zeta*J+invert (zeta*J)=3*GJ p := by
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K)≠0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h45 : (45 : K)≠0 := by
    rw [show (45 : K)=3^2*5 by ring]
    exact mul_ne_zero (pow_ne_zero _ h3) h5
  have hscale : (1/3 : K)*(1/5)=3*(1/45) := by
    field_simp [h3,h5,h45]
    ring
  have hs := congrArg (LaurentPolynomial.C : K →+* K[T;T⁻¹]) hscale
  simp only [map_mul,map_ofNat] at hs
  have hi : invert (phase p : K[T;T⁻¹])=phase p := by
    simp only [phase,map_sub,map_mul,map_ofNat,invert_T,neg_neg]
    ring
  dsimp only
  rw [original_zeta_phase p hp,GJ_phase]
  simp only [map_mul,Polynomial.toLaurent_C,invert_C,hi]
  linear_combination phase p*((HJP p).toLaurent+invert (HJP p).toLaurent)*hs

/-- The original one-third proper J contribution retains its mandatory two-Frobenius value. -/
theorem actual_native_J_normalization (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) :
    let zeta : K[T;T⁻¹] := LaurentPolynomial.C (1/3 : K)*T (-(p : ℤ))*
      (Abar : K[X]).toLaurent^p
    let J := (Polynomial.C (1/5 : K)*HJP p).toLaurent
    (LaurentPolynomial.C (1/3 : K)*(zeta*J+invert (zeta*J))).coeff
      (2*(p : ℤ))=-4*(HJP p : K[X]).coeff p/45 := by
  have h3 : (3 : K)≠0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have hc : (LaurentPolynomial.C (1/3 : K)*3 : K[T;T⁻¹])=1 := by
    change LaurentPolynomial.C (1/3 : K)*LaurentPolynomial.C (3 : K)=1
    rw [←map_mul,one_div_mul_cancel h3,map_one]
  dsimp only
  rw [actual_native_J_pair p hp,←mul_assoc,hc,one_mul,
    actual_GJ_2p_coefficient p hp]

end WPFieldAssembly.SourceClosureVbalJCarrierNormalization
