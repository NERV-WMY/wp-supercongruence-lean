import WPFieldAssembly.SourceClosureUVWeightedBands
import WPFieldAssembly.ActualUVSourceIdentification
import WPFiniteJWeightedResidue

open scoped LaurentPolynomial Polynomial
open Polynomial LaurentPolynomial WPFieldAssembly.ActualUVSourceIdentification
  WPFieldAssembly.ActualKwFieldTrace WPFieldAssembly.ActualKwWeightedTrace
  WPFieldAssembly.SourceClosureUVPhaseTrace WPFieldAssembly.SourceClosureUVWeightedBands

namespace WPFieldAssembly.SourceClosureUVWeightedLog

theorem weighted_add (p : ℕ) [Fact p.Prime] (F G : (ZMod p)[T;T⁻¹]) :
    originalWeightedFieldTrace p (F+G)=
      originalWeightedFieldTrace p F+originalWeightedFieldTrace p G := by
  simp only [originalWeightedFieldTrace, mul_add, map_add]

theorem weighted_sub (p : ℕ) [Fact p.Prime] (F G : (ZMod p)[T;T⁻¹]) :
    originalWeightedFieldTrace p (F-G)=
      originalWeightedFieldTrace p F-originalWeightedFieldTrace p G := by
  simp only [originalWeightedFieldTrace, mul_sub, map_sub]

theorem weighted_C_mul (p : ℕ) [Fact p.Prime] (c : ZMod p)
    (F : (ZMod p)[T;T⁻¹]) :
    originalWeightedFieldTrace p (LaurentPolynomial.C c*F)=
      c*originalWeightedFieldTrace p F := by
  unfold originalWeightedFieldTrace
  rw [show (3*(ActualKwFieldTrace.R : (ZMod p)[T;T⁻¹])^p*
      (3*T (-1)*(4-11*T 1)))*(LaurentPolynomial.C c*F)=
      LaurentPolynomial.C c*((3*ActualKwFieldTrace.R^p*(3*T (-1)*(4-11*T 1)))*F) by ring]
  exact ActualKwFieldTrace.fieldTrace_C_mul p (p+1) c _

end WPFieldAssembly.SourceClosureUVWeightedLog

open WPFieldAssembly.SourceClosureUVWeightedLog

namespace WPFieldAssembly.SourceClosureUVWeightedK0

/- The K0 contraction clears the entire original quadratic denominator.
   The low polynomial's origin is kept until the final scoped specialization. -/

theorem originalK0_quadratic_factor (p : ℕ) [Fact p.Prime] (hp : 19≤p) :
    (originalK0 p : (ZMod p)[T;T⁻¹]) =
      LaurentPolynomial.C (1/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        T (-(p : ℤ))*(LaurentPoleField.fieldAbar p).toLaurent^p := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 :=
    pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  have hc : (2/WPFiniteABSourceTail.epsilon p : ZMod p)=
      4*(1/(2*WPFiniteABSourceTail.epsilon p)) := by
    rw [mul_one_div]
    apply (div_eq_div_iff heps (mul_ne_zero h2 heps)).2
    ring
  have hc17 : (17/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)=
      17*(1/(2*WPFiniteABSourceTail.epsilon p)) := by ring
  let U : (ZMod p)[T;T⁻¹] := T (p : ℤ)
  let V : (ZMod p)[T;T⁻¹] := T (-(p : ℤ))
  let c : (ZMod p)[T;T⁻¹] := LaurentPolynomial.C
    (1/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)
  have hVU : V*U=1 := by
    dsimp only [V,U]
    rw [←T_add, neg_add_cancel, T_zero]
  have h2p : (T (2*(p : ℤ)) : (ZMod p)[T;T⁻¹])=U^2 := by
    dsimp only [U]
    rw [T_pow]
    norm_num
  rw [originalK0, hc, hc17, map_mul, map_mul, map_ofNat, map_ofNat,
    ←field_A, original_A_power, h2p]
  change 17*c-4*c*(U+V)=c*V*(-4*U^2+17*U-4)
  linear_combination c*(4*U-17)*hVU

/-- No Laurent support hypothesis is needed for the original K0 cancellation. -/
theorem originalK0_weight_source (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (F : (ZMod p)[T;T⁻¹]) :
    originalWeightedFieldTrace p (originalK0 p*F)=
      (3/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        endpointTrace (1/4 : ZMod p) 4 ((4*T (p : ℤ)-11)*F) := by
  have hR : (R : (ZMod p)[T;T⁻¹])^p*T (-(p : ℤ))=4*T (p : ℤ)-11 := by
    rw [original_R_power, sub_mul, mul_assoc, ←T_add,
      show 2*(p : ℤ)+(-(p : ℤ))=(p : ℤ) by omega,
      mul_assoc, ←T_add]
    simp
  have hclear : LaurentPoleField.fieldTrace p (p+1)
      ((LaurentPoleField.fieldAbar p).toLaurent^p*
        (3*R^p*T (-(p : ℤ))*(3*T (-1)*(4-11*T 1))*F)) =
      LaurentPoleField.fieldTrace p 1
        (3*R^p*T (-(p : ℤ))*(3*T (-1)*(4-11*T 1))*F) := by
    simpa only [Nat.add_comm] using LaurentPoleField.fieldTrace_cleared_pow p 1 p hp _
  unfold originalWeightedFieldTrace
  rw [originalK0_quadratic_factor p hp]
  rw [show (3*(R : (ZMod p)[T;T⁻¹])^p*(3*T (-1)*(4-11*T 1)))*
      ((LaurentPolynomial.C (1/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        T (-(p : ℤ))*(LaurentPoleField.fieldAbar p).toLaurent^p)*F) =
      LaurentPolynomial.C (1/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        ((LaurentPoleField.fieldAbar p).toLaurent^p*
          (3*R^p*T (-(p : ℤ))*(3*T (-1)*(4-11*T 1))*F)) by ring,
    fieldTrace_C_mul, hclear]
  rw [show (3*(R : (ZMod p)[T;T⁻¹])^p*T (-(p : ℤ))*
      (3*T (-1)*(4-11*T 1)))*F =
      LaurentPolynomial.C (3 : ZMod p)*
        (3*T (-1)*(4-11*T 1)*((R^p*T (-(p : ℤ)))*F)) by
        simp only [map_ofNat]
        ring, fieldTrace_C_mul, hR]
  change (1/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
    (3*fieldDlogQ p ((4*T (p : ℤ)-11)*F))=_
  rw [fieldDlogQ_endpoint p hp]
  ring

theorem infinityQ_endpoint (p : ℕ) [Fact p.Prime] (F : (ZMod p)[T;T⁻¹]) :
    WPFiniteJWeightedResidue.infinityQ F=endpointTrace (1/4 : ZMod p) 4 F := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => rw [WPFiniteJWeightedResidue.infinityQ_add, map_add, hF, hG]
  | C_mul_T n a =>
    rw [WPFiniteJWeightedResidue.infinityQ_single, endpointTrace_monomial]
    unfold endpointWeight
    split_ifs <;> ring

theorem lowBand_self (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X]) (hP : P.natDegree<p) :
    WPFiniteJHighCoefficient.lowBand (p+1) P=P := by
  ext j
  rw [WPFiniteJHighCoefficient.lowBand_coeff]
  by_cases hj : j<p+1
  · rw [if_pos hj]
  · rw [if_neg hj]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

theorem shifted_low_symmetric_endpoint (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (P : (ZMod p)[X]) (hP : P.natDegree<p) :
    endpointTrace (1/4 : ZMod p) 4
      (T (p : ℤ)*(P.toLaurent+invert P.toLaurent)) =
      -(33/4 : ZMod p)*(P.eval 4+P.eval (1/4)) := by
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h4p : (4 : ZMod p)^p=4 := ZMod.pow_card _
  have hap : (1/4 : ZMod p)^p=1/4 := ZMod.pow_card _
  have hPp : P.coeff p=0 := Polynomial.coeff_eq_zero_of_natDegree_lt hP
  have href4 := WPFiniteJWeightedResidue.trunc_shift_invert_eval P p (4 : ZMod p) h4
  have hrefa := WPFiniteJWeightedResidue.trunc_shift_invert_eval P p (1/4 : ZMod p)
    (one_div_ne_zero h4)
  rw [lowBand_self p P hP, h4p,
    show (4 : ZMod p)⁻¹=1/4 from (one_div (4 : ZMod p)).symm] at href4
  rw [lowBand_self p P hP, hap,
    show (1/4 : ZMod p)⁻¹=4 by rw [one_div, inv_inv]] at hrefa
  have hrc : (LaurentPolynomial.trunc (T (p : ℤ)*invert P.toLaurent)).coeff 0=0 := by
    rw [WPFiniteJWeightedResidue.trunc_coeff]
    have hs := WPFiniteJCarrier.shifted_coeff (1 : ZMod p) (p : ℤ) 0
      (invert P.toLaurent)
    simp only [map_one, one_mul, zero_sub, invert_apply, neg_neg,
      WPFiniteJCarrier.toLaurent_coeff_nat, hPp] at hs
    exact hs
  have hpoly : (T (p : ℤ) : (ZMod p)[T;T⁻¹])*P.toLaurent=(X^p*P).toLaurent := by
    rw [map_mul, Polynomial.toLaurent_X_pow]
  have hi : endpointTrace (1/4 : ZMod p) 4 (T (p : ℤ)*invert P.toLaurent)=
      -8*P.eval (1/4)-(1/4 : ZMod p)*P.eval 4 := by
    rw [←infinityQ_endpoint, WPFiniteJWeightedResidue.infinityQ, href4, hrefa, hrc]
    ring
  have hp' : endpointTrace (1/4 : ZMod p) 4 (T (p : ℤ)*P.toLaurent)=
      -8*P.eval 4-(1/4 : ZMod p)*P.eval (1/4) := by
    rw [hpoly, endpointTrace_polynomial, coeff_zero_eq_eval_zero]
    simp only [eval_mul, eval_pow, eval_X, h4p, hap,
      zero_pow (by omega : p≠0), zero_mul]
    ring
  rw [mul_add, map_add, hp', hi]
  field_simp [h4]
  ring

/-- This records the origin contribution instead of discarding it during reflection. -/
theorem originalK0_low_symmetric_weight (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (P : (ZMod p)[X]) (hP : P.natDegree<p) :
    originalWeightedFieldTrace p (originalK0 p*(P.toLaurent+invert P.toLaurent))=
      -(33/(2*WPFiniteABSourceTail.epsilon p) : ZMod p)*
        (2*P.eval (1/4)+P.eval 4+3*P.coeff 0) := by
  have h2 : (2 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p)≠0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have heps : (WPFiniteABSourceTail.epsilon p : ZMod p)≠0 :=
    pow_ne_zero _ (WPFiniteField.denominator_ne_zero p 5 (Finset.mem_Ico.mpr (by omega)))
  rw [originalK0_weight_source p hp, sub_mul,
    show (4 : (ZMod p)[T;T⁻¹])=LaurentPolynomial.C (4 : ZMod p) from
      (_root_.map_natCast (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) 4).symm,
    show (11 : (ZMod p)[T;T⁻¹])=LaurentPolynomial.C (11 : ZMod p) from
      (_root_.map_natCast (LaurentPolynomial.C : ZMod p →+* (ZMod p)[T;T⁻¹]) 11).symm,
    mul_assoc, map_sub, endpointTrace_C_mul, endpointTrace_C_mul,
    shifted_low_symmetric_endpoint p hp P hP, map_add,
    endpointTrace_polynomial, endpointTrace_inverted_polynomial]
  field_simp [h2, h4, heps]
  ring

end WPFieldAssembly.SourceClosureUVWeightedK0
