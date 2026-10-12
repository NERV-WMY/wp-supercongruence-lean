import WPFieldAssembly.NativeClosureEndProduct

open scoped Polynomial LaurentPolynomial
open Polynomial
open LaurentPolynomial (T invert invert_apply invert_T trunc)
open WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.ActualSimplePoleResidue

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

private theorem endProduct_trunc_shift_one (F : K[T;T⁻¹]) :
    trunc (T (-1) * F) = (trunc F).divX := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff, coeff_divX,
    WPFiniteJWeightedResidue.trunc_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (j : ℤ) F
  simp only [map_one, one_mul] at hs
  rw [hs]
  congr 1

/-- Clearing Abar and retaining both divided differences gives the actual affine density. -/
theorem endProduct_affine_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (r s : K) (F : K[T;T⁻¹]) :
    originPole ((LaurentPolynomial.C r + LaurentPolynomial.C s * T 1) * F) =
      ((r + s / 4) / 15) * (DD (1 / 4 : K) 4 F).coeff (-1) -
        ((r + 4 * s) / 15) * (DD (4 : K) (1 / 4) F).coeff (-1) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 15
    (Finset.mem_Ico.mpr (by omega))
  let P : K[X] := trunc (invert F)
  have ha := congrArg (fun Q : K[X] => Q.eval (1 / 4)) (X_mul_divX_add P)
  have hb := congrArg (fun Q : K[X] => Q.eval 4) (X_mul_divX_add P)
  simp only [eval_add, eval_mul, eval_X, eval_C] at ha hb
  have h0 : P.coeff 0 = F.coeff 0 := by
    change (invert F).coeff 0 = F.coeff 0
    simp only [invert_apply, neg_zero]
  have he : (LaurentPolynomial.C r + LaurentPolynomial.C s * T 1) * F =
      LaurentPolynomial.C r * F + LaurentPolynomial.C s * (T 1 * F) := by ring
  rw [he, originPole_add, originPole_C_mul, originPole_C_mul,
    originPole_trunc_inverse, originPole_trunc_inverse, map_mul, invert_T,
    endProduct_trunc_shift_one, endProduct_pole_origin, endProduct_pole_origin]
  change r * ((P.eval (1 / 4) - P.eval 4) / 15) +
      s * ((P.divX.eval (1 / 4) - P.divX.eval 4) / 15) =
    ((r + s / 4) / 15) * (-P.eval 4 + F.coeff 0) -
      ((r + 4 * s) / 15) * (-P.eval (1 / 4) + F.coeff 0)
  rw [← h0]
  linear_combination (norm := (field_simp [h4, h15]; ring))
    (4 * s / 15) * ha - (s / 15 / 4) * hb

theorem endProduct_dlogV_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (F : K[T;T⁻¹]) :
    originPole ((LaurentPolynomial.C (33 : K) - LaurentPolynomial.C (12 : K) * T 1) * F) =
      2 * (DD (1 / 4 : K) 4 F).coeff (-1) + (DD (4 : K) (1 / 4) F).coeff (-1) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 15
    (Finset.mem_Ico.mpr (by omega))
  have he : (LaurentPolynomial.C (33 : K) - LaurentPolynomial.C (12 : K) * T 1 :
      K[T;T⁻¹]) = LaurentPolynomial.C (33 : K) + LaurentPolynomial.C (-12 : K) * T 1 := by
    rw [map_neg]
    ring
  rw [he, endProduct_affine_density p hp]
  have ha : ((33 : K) + -12 / 4) / 15 = 2 := by field_simp [h4, h15]; ring
  have hb : ((33 : K) + 4 * -12) / 15 = -1 := by field_simp [h4, h15]; ring
  rw [ha, hb]
  ring

end WPFieldAssembly.ActualBpairContraction
