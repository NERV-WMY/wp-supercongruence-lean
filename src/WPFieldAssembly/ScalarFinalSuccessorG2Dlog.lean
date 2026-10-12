import WPFieldAssembly.ActualBpairMixedTail
import WPFieldAssembly.ActualSimplePoleResidue

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
open WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 2400000

/- This whole-support functional identity is the original logarithmic-density
step used by all five G2 tails. It is checked independently of their numerical
evaluation. No carrier, scalar or residue value is supplied by the caller. -/

private theorem trunc_shift_minus_one (F : K[T;T⁻¹]) :
    trunc (T (-1)*F)=(trunc F).divX := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff,coeff_divX,
    WPFiniteJWeightedResidue.trunc_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (j : ℤ) F
  simp only [map_one,one_mul] at hs
  rw [hs]
  congr 1

/-- The original logarithmic density sees every negative coefficient and its true origin. -/
theorem original_dlogV_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (F : K[T;T⁻¹]) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*F)=
      -fullStrictTail p 0 (invert F) := by
  let P : K[X] := trunc (invert F)
  have ha := congrArg (fun Q : K[X] => Q.eval (1/4)) (X_mul_divX_add P)
  have hb := congrArg (fun Q : K[X] => Q.eval 4) (X_mul_divX_add P)
  simp only [eval_add,eval_mul,eval_X,eval_C] at ha hb
  have he : (LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*F=
      LaurentPolynomial.C (33 : K)*F-
        LaurentPolynomial.C (12 : K)*(T 1*F) := by ring
  rw [he,originPole_sub,originPole_C_mul,originPole_C_mul,
    originPole_trunc_inverse,originPole_trunc_inverse,map_mul,invert_T,
    trunc_shift_minus_one]
  simp only [fullStrictTail,fullStrictPositive,Nat.zero_mul,Nat.cast_zero,neg_zero,
    T_zero,one_mul,eval_sub,eval_C]
  change (33 : K)*((P.eval (1/4)-P.eval 4)/15)-
    (12 : K)*((P.divX.eval (1/4)-P.divX.eval 4)/15)=
      -(2*(P.eval 4-(invert F).coeff 0)+(P.eval (1/4)-(invert F).coeff 0))
  have h0 : P.coeff 0=(invert F).coeff 0 := rfl
  rw [←h0]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by
    rw [show (15 : K) = 3*5 by ring]
    exact mul_ne_zero h3 h5
  linear_combination (norm := (field_simp [h3,h4,h5,h15]; ring))
      -(16/5 : K)*ha+(1/5 : K)*hb

theorem fullStrictTail_zero_negative_phase (p k : ℕ) (F : K[T;T⁻¹]) :
    fullStrictTail p 0 (T (-((k*p : ℕ) : ℤ))*F)=fullStrictTail p k F := by
  have he : fullStrictPositive p 0 (T (-((k*p : ℕ) : ℤ))*F)=fullStrictPositive p k F := by
    ext j
    rw [fullStrictPositive_coeff,fullStrictPositive_coeff]
    by_cases hj : j=0
    · rw [if_pos hj,if_pos hj]
    · rw [if_neg hj,if_neg hj]
      have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-((k*p : ℕ) : ℤ))
        ((0*p+j : ℕ) : ℤ) F
      simp only [map_one,one_mul] at hs
      rw [hs]
      congr 1
      push_cast
      ring
  rw [fullStrictTail,fullStrictTail,he]

/-- No upper cutoff is introduced when the original reciprocal source is shifted. -/
theorem original_dlogV_inverse_phase (p k : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19≤p) (F : K[T;T⁻¹]) :
    originPole ((LaurentPolynomial.C (33 : K)-LaurentPolynomial.C (12 : K)*T 1)*
      (T ((k*p : ℕ) : ℤ)*invert F))=-fullStrictTail p k F := by
  rw [original_dlogV_residue p hp,map_mul,invert_T,involutive_invert F,
    fullStrictTail_zero_negative_phase]

end WPFieldAssembly.ActualBpairContraction
