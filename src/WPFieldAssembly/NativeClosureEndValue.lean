import WPFieldAssembly.NativeClosureEndBands
import WPFieldAssembly.NativeClosureKernelValues
import WPFieldAssembly.ActualKwOrderedEndpoints

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPActualCanonicalFinitePart WPCartierPoleProjection
open WPFieldAssembly.GreenLaurentOperators
open WPFiniteAffineLog

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000


/-- The derivative is evaluated on the complete end source with its real -p coefficient. -/
theorem endKernel_derivative_raw (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (literalKB (K := ZMod p) p * D (endKernelChi0 p)).coeff (-1) =
      -(3 / 10 : ZMod p) * (Dstar p : (ZMod p)[X]).coeff 0 -
        281 * WPFiniteNC122.q p / 30 - 2 * WPFiniteNC122.h p +
        (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) / 2 -
        WPFiniteField.ell p (16 : ZMod p) / 5 := by
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 2 h2 using 1; norm_num
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 5
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 4 h2 using 1; norm_num
  have h16p : (16 : ZMod p) ^ p = 16 := ZMod.pow_card _
  have hinv := WPFiniteField.ell_inversion p (16 : ZMod p) h16
  rw [h16p] at hinv
  have h1 : WPFiniteField.ell p (1 : ZMod p) = 0 :=
    (WPFiniteCubicJ.rational_ell_sources (K := ZMod p) p hp).1
  have hpow : (4 : ZMod p) ^ (-(p : ℤ)) = 1 / 4 := by
    rw [zpow_neg, zpow_natCast, ZMod.pow_card, one_div]
  have hapow : (1 / 4 : ZMod p) ^ (-(p : ℤ)) = 4 := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow, ZMod.pow_card, inv_inv]
  have hw1 := endKernelW1_degree (K := ZMod p) p hp
  have hd := original_kernel_derivative_with_slots p hp (endKernelChi0 p)
    (fun j hj => Finset.mem_Icc.mpr (by
      have hs := endKernelChi0_support (K := ZMod p) p hp j hj
      constructor <;> omega))
  obtain ⟨hz, hm, hpcoeff⟩ := endKernelChi0_invisible_coefficients (K := ZMod p) p hp
  rw [hz, hm, hpcoeff, mul_zero, add_zero] at hd
  have ha0 := kernel_valueAt_shifted_polynomial p (endKernelW0 p) 0 (1 / 4) (one_div_ne_zero h4)
  have hb0 := kernel_valueAt_shifted_polynomial p (endKernelW0 p) 0 4 h4
  have ha1 := kernel_valueAt_shifted_polynomial p (endKernelW1 p) (-(p : ℤ))
    (1 / 4) (one_div_ne_zero h4)
  have hb1 := kernel_valueAt_shifted_polynomial p (endKernelW1 p) (-(p : ℤ)) 4 h4
  simp only [T_zero, one_mul, zpow_zero] at ha0 hb0
  rw [hapow] at ha1
  rw [hpow] at hb1
  have hna := kernel_negativeValue_negative_phase p (endKernelW1 p) (by omega) (1 / 4)
  have hnb := kernel_negativeValue_negative_phase p (endKernelW1 p) (by omega) 4
  have hv : originalKernelValue p (endKernelChi0 p) =
      (29 / 6 : ZMod p) * ((endKernelW0 p).eval (1 / 4) + 4 * (endKernelW1 p).eval (1 / 4)) -
      (23 / 6 : ZMod p) * ((endKernelW0 p).eval 4 + (1 / 4) * (endKernelW1 p).eval 4) +
      2 * (-8 * (endKernelW1 p).eval (1 / 4) - (1 / 4) * (endKernelW1 p).eval 4) := by
    unfold originalKernelValue endKernelChi0
    rw [kernel_valueAt_add, kernel_valueAt_add, kernel_negativeValue_add,
      kernel_negativeValue_add, ha0, hb0,
      kernel_negativeValue_polynomial, kernel_negativeValue_polynomial,
      hna, hnb, ha1, hb1]
    ring
  rw [hv] at hd
  obtain ⟨hda, hdb⟩ := Dstar_endpoints (K := ZMod p) p hp
  have hprod : (1 / 4 : ZMod p) * (1 / 4) = 1 / 16 := by field_simp [h4, h16]; ring
  have hprod' : (4 : ZMod p) * 4 = 16 := by ring
  have hacancel : (1 / 4 : ZMod p) * 4 = 1 := one_div_mul_cancel h4
  have hbcancel : (4 : ZMod p) * (1 / 4) = 1 := mul_one_div_cancel h4
  simp only [endKernelW0, endKernelW1, eval_add, eval_sub, eval_mul, eval_neg,
    eval_C, eval_comp, eval_X, LP_eval_eq, hprod, hprod', hacancel, hbcancel,
    hda, hdb, h1] at hd
  rw [show (1 / 16 : ZMod p) = (16 : ZMod p)⁻¹ by rw [one_div], hinv] at hd
  -- The literal slot calculation gives -3*D0/10-197*q/30-5*h/3-ell16/6.
  -- Its printed SB107 representative uses the proved rational finite-log relation.
  have hfinite : WPFiniteField.ell p (16 : ZMod p) +
      84 * WPFiniteNC122.q p + 10 * WPFiniteNC122.h p -
        15 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) = 0 := by
    have he := (ActualKwOrderedEndpoints.finiteLog_c_ordered_zmod p hp).2.2
    change WPFiniteField.ell p (16 : ZMod p) = _ at he
    rw [he]
    dsimp only [WPFiniteNC122.q, WPFiniteNC122.h]
    field_simp [h2]
    ring
  have h6 : (6 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h3 using 1
    norm_num
  have h8 : (8 : ZMod p) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1
    norm_num
  have h10 : (10 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1
    norm_num
  have h15 : (15 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h3 h5 using 1
    norm_num
  have h30 : (30 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h6 h5 using 1
    norm_num
  linear_combination (norm := (field_simp [h2, h3, h4, h5, h6, h8, h10, h15, h16, h30]; ring))
    hd + (1 / 30 : ZMod p) * hfinite

/-- The original derivative after the already checked rational finite-log reduction. -/
theorem endKernel_derivative_rational (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (literalKB (K := ZMod p) p * D (endKernelChi0 p)).coeff (-1) =
      -(3 / 10 : ZMod p) * (Dstar p : (ZMod p)[X]).coeff 0 +
        223 * WPFiniteNC122.q p / 30 -
          5 * (WPFiniteInversion.integerFermatQuotient p 5 : ZMod p) / 2 := by
  have he := (ActualKwOrderedEndpoints.finiteLog_c_ordered_zmod p hp).2.2
  change WPFiniteField.ell p (16 : ZMod p) = _ at he
  rw [endKernel_derivative_raw p hp, he]
  dsimp only [WPFiniteNC122.q, WPFiniteNC122.h]
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero (K := ZMod p) p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h2 h5 using 1
    norm_num
  have h30 : (30 : ZMod p) ≠ 0 := by
    convert mul_ne_zero h3 h10 using 1
    norm_num
  field_simp [h2, h5, h10, h30]
  ring

end WPFieldAssembly.ActualBpairContraction
