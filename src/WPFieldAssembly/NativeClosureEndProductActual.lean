import WPFieldAssembly.NativeClosureEndProduct
import WPFieldAssembly.ScalarFinalSuccessorUniversalEndDensity
import WPFieldAssembly.NativeClosureEndKernel
import WPFieldAssembly.NativeClosureInclusiveTail
import WPFieldAssembly.ActualKwOrderedEndpoints
import WPFieldAssembly.ActualKwRationalRowAttachment
import WPFieldAssembly.NativeClosureEndTransport

open scoped Polynomial LaurentPolynomial BigOperators
open Polynomial WPFiniteAffineLog WPFiniteProductTail
open LaurentPolynomial (T invert invert_apply invert_T trunc)
open WPFieldAssembly.GreenLaurentOperators WPFieldAssembly.ActualSimplePoleResidue
open WPFieldAssembly.ActualCubicNativeSource WPFieldAssembly.ActualKwOrderedEndpoints

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

private theorem endProduct_denominator_units (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (4 : K) ≠ 0 ∧
    (6 : K) ≠ 0 ∧
    (10 : K) ≠ 0 ∧
    (12 : K) ≠ 0 ∧
    (15 : K) ≠ 0 ∧
    (16 : K) ≠ 0 ∧
    (18 : K) ≠ 0 ∧
    (20 : K) ≠ 0 ∧
    (30 : K) ≠ 0 ∧
    (40 : K) ≠ 0 ∧
    (45 : K) ≠ 0 ∧
    (60 : K) ≠ 0 ∧
    (90 : K) ≠ 0 ∧
    (120 : K) ≠ 0 ∧
    (240 : K) ≠ 0 ∧
    (480 : K) ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have hs (a b c : ℕ) : ((2 : K)^a * 3^b * 5^c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero a h2) (pow_ne_zero b h3))
      (pow_ne_zero c h5)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hs 2 0 0 using 1; norm_num
  · convert hs 1 1 0 using 1; norm_num
  · convert hs 1 0 1 using 1; norm_num
  · convert hs 2 1 0 using 1; norm_num
  · convert hs 0 1 1 using 1; norm_num
  · convert hs 4 0 0 using 1; norm_num
  · convert hs 1 2 0 using 1; norm_num
  · convert hs 2 0 1 using 1; norm_num
  · convert hs 1 1 1 using 1; norm_num
  · convert hs 3 0 1 using 1; norm_num
  · convert hs 0 2 1 using 1; norm_num
  · convert hs 2 1 1 using 1; norm_num
  · convert hs 1 2 1 using 1; norm_num
  · convert hs 3 1 1 using 1; norm_num
  · convert hs 4 1 1 using 1; norm_num
  · convert hs 5 1 1 using 1; norm_num


noncomputable def endProductK0 (p : ℕ) : K[X] :=
  C (1 / 6 : K) * (C (35 : K) * (LP p).comp (C (1 / 4 : K) * X) -
    C (5 : K) * (LP p).comp (C (4 : K) * X))

noncomputable def endProductK1 (p : ℕ) : K[X] :=
  C (1 / 6 : K) * (C (92 : K) * (LP p).comp (C (1 / 4 : K) * X) -
    C (29 * (1 / 4) : K) * (LP p).comp (C (4 : K) * X))

noncomputable def endProductK2 (p : ℕ) : K[X] :=
  C (1 / 6 : K) * (C (368 : K) * (LP p).comp (C (1 / 4 : K) * X) -
    C (29 * (1 / 4) ^ 2 : K) * (LP p).comp (C (4 : K) * X))

/-- The original e before its SB72 primitive scaling. -/
noncomputable def endProductE (p : ℕ) : K[X] :=
  (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate

/-- The polynomial bands reassemble the full original Laurent kernel. -/
theorem endProduct_original_kernel (p : ℕ) :
    endProductKernel p (endProductK0 p) (endProductK1 p) (endProductK2 p) =
      literalKB (K := K) p := by
  simp only [endProductKernel, endProductK0, endProductK1, endProductK2,
    literalKB, kernelLog, map_mul, map_sub, Polynomial.toLaurent_C]
  norm_num
  have h92 : LaurentPolynomial.C (92 : K) =
      LaurentPolynomial.C (23 : K) * LaurentPolynomial.C (4 : K) := by
    rw [← map_mul]
    congr 1
    ring
  have h368 : LaurentPolynomial.C (368 : K) =
      LaurentPolynomial.C (23 : K) * LaurentPolynomial.C (16 : K) := by
    rw [← map_mul]
    congr 1
    ring
  rw [h92, h368]
  ring

private theorem endProduct_scaled_log_degree (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (C c * X)).natDegree ≤ p - 1 := by
  have hc : (C c * X : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul (LP_natDegree_le p) hc).trans (by simp))

theorem endProduct_kernel_degrees (p : ℕ) :
    (endProductK0 p : K[X]).natDegree ≤ p - 1 ∧
      (endProductK1 p : K[X]).natDegree ≤ p - 1 ∧
      (endProductK2 p : K[X]).natDegree ≤ p - 1 := by
  have ha := endProduct_scaled_log_degree (K := K) p (1 / 4)
  have hb := endProduct_scaled_log_degree (K := K) p 4
  unfold endProductK0 endProductK1 endProductK2
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply (natDegree_C_mul_le _ _).trans
    apply (natDegree_sub_le _ _).trans
    exact max_le ((natDegree_C_mul_le _ _).trans ha)
      ((natDegree_C_mul_le _ _).trans hb)

theorem endProduct_E_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (endProductE p : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  have hs : (WPFiniteWSource.squaredCoordinate : K[X]).natDegree ≤ 1 := by
    unfold WPFiniteWSource.squaredCoordinate
    exact (natDegree_C_mul_le _ _).trans
      ((natDegree_add_le _ _).trans (by simp))
  exact natDegree_comp_le.trans
    ((Nat.mul_le_mul (WPFiniteWSource.deltaE_degree (K := K) p hp) hs).trans (by omega))

/-- Both rational phases are proved for the characteristic-p field itself. -/
theorem endProduct_rational_phases (p : ℕ) [Fact p.Prime] [CharP K p] :
    (1 / 4 : K) ^ (-(p : ℤ)) = 4 ∧ (4 : K) ^ (-(p : ℤ)) = 1 / 4 := by
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  constructor
  · rw [zpow_neg, zpow_natCast, one_div, inv_pow, h4p, inv_inv]
  · rw [zpow_neg, zpow_natCast, h4p, one_div]

/-- The proper-end values come from the whole original two-band source. -/
theorem endProduct_actual_source_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endKernelW0 p : K[X]).eval (1 / 4) + 4 * (endKernelW1 p).eval (1 / 4) =
        WPFiniteNC122.q p ∧
      (endKernelW0 p : K[X]).eval 4 + (1 / 4 : K) * (endKernelW1 p).eval 4 =
        -WPFiniteNC122.q p := by
  have hn (n : ℕ) (hpos : 0 < n) (hlt : n < p) : (n : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p n (Finset.mem_Ico.mpr ⟨hpos, hlt⟩)
  have h2 : (2 : K) ≠ 0 := hn 2 (by omega) (by omega)
  have h3 : (3 : K) ≠ 0 := hn 3 (by omega) (by omega)
  have h4 : (4 : K) ≠ 0 := hn 4 (by omega) (by omega)
  have h5 : (5 : K) ≠ 0 := hn 5 (by omega) (by omega)
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have h6 : (6 : K) ≠ 0 := hn 6 (by omega) (by omega)
  have h15 : (15 : K) ≠ 0 := hn 15 (by omega) (by omega)
  have h16 : (16 : K) ≠ 0 := hn 16 (by omega) (by omega)
  have h16p : (16 : K) ^ p = 16 := WPFiniteField.natCast_pow_char p 16
  have hinv := WPFiniteField.ell_inversion p (16 : K) h16
  rw [h16p] at hinv
  have h1 : WPFiniteField.ell p (1 : K) = 0 :=
    (WPFiniteCubicJ.rational_ell_sources (K := K) p hp).1
  have hl := (finiteLog_c_ordered (K := K) p hp).2
  change WPFiniteField.ell p (16 : K) = _ at hl
  have haa : (1 / 4 : K) * (1 / 4) = 1 / 16 := by field_simp [h4, h16]; ring
  have hab : (1 / 4 : K) * 4 = 1 := one_div_mul_cancel h4
  have hba : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  have hbb : (4 : K) * 4 = 16 := by ring
  obtain ⟨hda, hdb⟩ := Dstar_endpoints (K := K) p hp
  simp only [endKernelW0, endKernelW1, eval_add, eval_sub, eval_mul, eval_neg,
    eval_C, eval_comp, eval_X, LP_eval_eq, haa, hab, hba, hbb, hda, hdb, h1]
  rw [show (1 / 16 : K) = (16 : K)⁻¹ by rw [one_div], hinv, hl]
  dsimp only [WPFiniteNC122.h, WPFiniteNC122.q]
  constructor <;> field_simp [h2, h3, h4, h5, h6, h15, h16, hu12] <;> ring

/-- The actual P carrier selects the same two bands, before any evaluation. -/
theorem endProduct_actual_P_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
      ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p)) =
        endProductSource p (endKernelW0 p) (endKernelW1 p) := by
  rw [actual_P_endKernel_source p hp u hu]
  rfl

theorem endProduct_W0_E (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (endKernelW0 p : K[X]) = C (2 / 5 : K) * endProductE p +
      C (11 * WPFiniteNC122.q p / 15 -
        (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have hc : (6 / 5 : K) * (1 / 3) = 2 / 5 := by field_simp [h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]; ring
  unfold endKernelW0 Dstar endProductE
  rw [show -C (6 / 5 : K) * (-C (1 / 3 : K) *
      (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate) =
    C ((6 / 5 : K) * (1 / 3)) *
      (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate by
        rw [map_mul]; ring, hc]

theorem endProduct_first_high_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    endProductHigh p ((endProductK1 p : K[X]) * endKernelW0 p) =
      C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p) := by
  have hk := (endProduct_kernel_degrees (K := K) p).2.1
  have hks : (endProductK1 p : K[X]).natDegree < p := by omega
  let c : K := 11 * WPFiniteNC122.q p / 15 -
    (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2
  have he : (endProductK1 p : K[X]) * endKernelW0 p =
      C (2 / 5 : K) * (endProductK1 p * endProductE p) + C c * endProductK1 p := by
    rw [endProduct_W0_E p hp]
    dsimp only [c]
    ring
  rw [he, endProductHigh_add, endProductHigh_C_mul, endProductHigh_C_mul,
    endProductHigh_small p _ hks, mul_zero, add_zero]

/-- The full SB107e cancellation consumes the actual kernel and the actual two bands. -/
theorem endProduct_actual_cancellation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -2 * (DD (1 / 4 : K) 4 (literalKB p * endKernelChi0 p)).coeff (-1) -
      (DD (4 : K) (1 / 4) (literalKB p * endKernelChi0 p)).coeff (-1) +
      2 * WPFiniteNC122.q p * (DD (1 / 4 : K) 4 (literalKB p)).coeff (-1) -
      WPFiniteNC122.q p * (DD (4 : K) (1 / 4) (literalKB p)).coeff (-1) =
      8 * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval 4 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hk0, hk1, hk2⟩ := endProduct_kernel_degrees (K := K) p
  have hw0 := endKernelW0_degree (K := K) p hp
  have hw1 := endKernelW1_degree (K := K) p hp
  have hf2 : ((endProductK2 p : K[X]) * endKernelW0 p +
      endProductK1 p * endKernelW1 p).natDegree < 2 * p := by
    apply (natDegree_add_le _ _).trans_lt
    apply max_lt
    · exact natDegree_mul_le.trans_lt (by omega)
    · exact natDegree_mul_le.trans_lt (by omega)
  have hf3 : ((endProductK2 p : K[X]) * endKernelW1 p).natDegree < 3 * p :=
    natDegree_mul_le.trans_lt (by omega)
  obtain ⟨hphasea, hphaseb⟩ := endProduct_rational_phases (K := K) p
  obtain ⟨ha, hb⟩ := endProduct_actual_source_ends (K := K) p hp
  have he := endProduct_whole_cancellation p (endProductK0 p) (endProductK1 p)
    (endProductK2 p) (endKernelW0 p) (endKernelW1 p) (WPFiniteNC122.q p)
    h4 (by omega) (by omega) hf2 hf3 (by simpa only [hphasea] using ha)
      (by simpa only [hphaseb] using hb)
  rw [endProduct_original_kernel] at he
  change -2 * (DD (1 / 4 : K) 4 (literalKB p * endKernelChi0 p)).coeff (-1) -
      (DD (4 : K) (1 / 4) (literalKB p * endKernelChi0 p)).coeff (-1) +
      2 * WPFiniteNC122.q p * (DD (1 / 4 : K) 4 (literalKB p)).coeff (-1) -
      WPFiniteNC122.q p * (DD (4 : K) (1 / 4) (literalKB p)).coeff (-1) = _ at he
  rw [hphasea, hphaseb, endProduct_first_high_source p hp] at he
  simpa only [show (2 : K) * 4 = 8 by ring] using he

/-- The same residue equality is attached to the complete actual P carrier. -/
theorem endProduct_actual_P_cancellation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    -2 * (DD (1 / 4 : K) 4 (literalKB p *
      (WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
        ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p))))).coeff (-1) -
      (DD (4 : K) (1 / 4) (literalKB p *
        (WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
          ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p))))).coeff (-1) +
      2 * WPFiniteNC122.q p * (DD (1 / 4 : K) 4 (literalKB p)).coeff (-1) -
      WPFiniteNC122.q p * (DD (4 : K) (1 / 4) (literalKB p)).coeff (-1) =
      8 * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval 4 := by
  rw [actual_P_endKernel_source p hp u hu]
  exact endProduct_actual_cancellation p hp

/-- Lambda_end is the original 2q/(x-a)-q/(x-b), with the complete kernel still present. -/
theorem endProduct_Lambda_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (q : K) (F : K[T;T⁻¹]) :
    originPole ((LaurentPolynomial.C (31 * q) - LaurentPolynomial.C (4 * q) * T 1) * F) =
      2 * q * (DD (1 / 4 : K) 4 F).coeff (-1) -
        q * (DD (4 : K) (1 / 4) F).coeff (-1) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 15
    (Finset.mem_Ico.mpr (by omega))
  have he : (LaurentPolynomial.C (31 * q) - LaurentPolynomial.C (4 * q) * T 1 :
      K[T;T⁻¹]) = LaurentPolynomial.C (31 * q) + LaurentPolynomial.C (-(4 * q)) * T 1 := by
    rw [map_neg]
    ring
  rw [he, endProduct_affine_density p hp]
  have ha : ((31 * q : K) + -(4 * q) / 4) / 15 = 2 * q := by
    field_simp [h4, h15]
    ring
  have hb : ((31 * q : K) + 4 * -(4 * q)) / 15 = q := by
    field_simp [h4, h15]
    ring
  rw [ha, hb]

/-- The complete original residue, rather than a prescribed endpoint functional. -/
theorem endProduct_actual_density_cancellation (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -originPole ((LaurentPolynomial.C (33 : K) - LaurentPolynomial.C (12 : K) * T 1) *
      (literalKB p * endKernelChi0 p)) +
      originPole ((LaurentPolynomial.C (31 * WPFiniteNC122.q p) -
        LaurentPolynomial.C (4 * WPFiniteNC122.q p) * T 1) * literalKB p) =
      8 * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductK0 p * endKernelW1 p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval 4 := by
  rw [endProduct_dlogV_density p hp, endProduct_Lambda_density p hp]
  convert endProduct_actual_cancellation (K := K) p hp using 1; ring

theorem endProduct_high_inclusive (p : ℕ) (P : K[X]) :
    endProductHigh p P = X ^ p * inclusivePositive p P := rfl

/-- SB107f retains the diagonal p coefficient of the original e logarithm product. -/
theorem endProduct_E_log_high_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (c : K) (hc : c ≠ 0) (z : K)
    (hcp : c ^ p = c) (hzp : z ^ p = z) :
    (endProductHigh p ((endProductE p : K[X]) * (LP p).comp (C c * X))).eval z =
      -(c * z) * unitPrimitive p (endProductE p) z c⁻¹ := by
  have he := endProduct_E_degree (K := K) p hp
  have hs := inclusive_log_high_frobenius p (endProductE p) (by omega) c hc z hcp hzp
  simpa only [endProductHigh, inclusivePositive, eval_mul, eval_pow, eval_X] using hs

/-- All four rational products use actual field Frobenius, with no added scalar premise. -/
theorem endProduct_E_log_high_four (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endProductHigh p ((endProductE p : K[X]) * (LP p).comp (C (1 / 4 : K) * X))).eval (1 / 4) =
      -((1 / 4 : K) * (1 / 4)) * unitPrimitive p (endProductE p) (1 / 4) 4 ∧
    (endProductHigh p ((endProductE p : K[X]) * (LP p).comp (C (1 / 4 : K) * X))).eval 4 =
      -((1 / 4 : K) * 4) * unitPrimitive p (endProductE p) 4 4 ∧
    (endProductHigh p ((endProductE p : K[X]) * (LP p).comp (C (4 : K) * X))).eval (1 / 4) =
      -((4 : K) * (1 / 4)) * unitPrimitive p (endProductE p) (1 / 4) (1 / 4) ∧
    (endProductHigh p ((endProductE p : K[X]) * (LP p).comp (C (4 : K) * X))).eval 4 =
      -((4 : K) * 4) * unitPrimitive p (endProductE p) 4 (1 / 4) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have ha : (1 / 4 : K) ≠ 0 := one_div_ne_zero h4
  have h4p : (4 : K) ^ p = 4 := WPFiniteField.natCast_pow_char p 4
  have hap : (1 / 4 : K) ^ p = 1 / 4 := by rw [one_div, inv_pow, h4p]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [one_div, inv_inv] using
      endProduct_E_log_high_frobenius p hp (1 / 4) ha (1 / 4) hap hap
  · simpa only [one_div, inv_inv] using
      endProduct_E_log_high_frobenius p hp (1 / 4) ha 4 hap h4p
  · simpa only [one_div] using
      endProduct_E_log_high_frobenius p hp 4 h4 (1 / 4) h4p hap
  · simpa only [one_div] using
      endProduct_E_log_high_frobenius p hp 4 h4 4 h4p h4p

/- The remaining SB107 contraction uses only full finite logarithms.  The
strict low operator below is the complement of the inclusive p tail already
used above; neither its p coefficient nor a negative Laurent phase is lost. -/

theorem endProductLow_eq_lowBand (p : ℕ) (P : K[X]) :
    endProductLow p P = WPFiniteJHighCoefficient.lowBand p P := by
  ext j
  rw [endProductLow_coeff, WPFiniteJHighCoefficient.lowBand_coeff]

private theorem endProductLow_add (p : ℕ) (P Q : K[X]) :
    endProductLow p (P + Q) = endProductLow p P + endProductLow p Q := by
  rw [endProductLow, endProductLow, endProductLow, endProductHigh_add]
  ring

private theorem endProductLow_sub (p : ℕ) (P Q : K[X]) :
    endProductLow p (P - Q) = endProductLow p P - endProductLow p Q := by
  ext j
  simp only [endProductLow_coeff, coeff_sub]
  split_ifs <;> ring

private theorem endProductLow_C_mul (p : ℕ) (c : K) (P : K[X]) :
    endProductLow p (C c * P) = C c * endProductLow p P := by
  rw [endProductLow, endProductLow, endProductHigh_C_mul]
  ring

private theorem endProductLow_sum {ι : Type*} (p : ℕ) (S : Finset ι) (P : ι → K[X]) :
    endProductLow p (∑ i ∈ S, P i) = ∑ i ∈ S, endProductLow p (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [endProductLow, endProductHigh]
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, endProductLow_add, hS]

private theorem endProductLow_monomial (p n : ℕ) (c : K) :
    endProductLow p (C c * X ^ n) = if n < p then C c * X ^ n else 0 := by
  ext j
  rw [endProductLow_coeff]
  by_cases hn : n < p
  · rw [if_pos hn]
    by_cases hj : j < p
    · rw [if_pos hj]
    · rw [if_neg hj, coeff_C_mul_X_pow, if_neg (by omega)]
  · rw [if_neg hn, coeff_zero]
    by_cases hj : j < p
    · rw [if_pos hj, coeff_C_mul_X_pow, if_neg (by omega)]
    · rw [if_neg hj]

private theorem endProduct_scaled_log_sum (p : ℕ) (c : K) :
    (LP p : K[X]).comp (C c * X) =
      ∑ j ∈ Finset.Ico 1 p, C (c ^ j / (j : K)) * X ^ j := by
  unfold LP
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow,
    ← mul_assoc, ← C_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp only [div_eq_mul_inv]
  ring

/-- The actual low product is the full unit triangle T2, not the full square. -/
theorem endProduct_low_log_T2 (p : ℕ) [Fact p.Prime] [CharP K p] (a b z : K) :
    (endProductLow p (((LP p : K[X]).comp (C a * X)) *
      ((LP p).comp (C b * X)))).eval z =
        WPFiniteDReciprocity.T2 p (a * z) (b * z) := by
  rw [endProduct_scaled_log_sum, endProduct_scaled_log_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [endProductLow_sum, eval_finsetSum]
  simp_rw [endProductLow_sum, eval_finsetSum]
  have hm (i j : ℕ) :
      (C (a ^ i / (i : K)) * X ^ i : K[X]) *
        (C (b ^ j / (j : K)) * X ^ j) =
          C (a ^ i * b ^ j / ((i : K) * (j : K))) * X ^ (i + j) := by
    rw [mul_mul_mul_comm, ← C_mul, ← pow_add]
    congr 1
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hm, endProductLow_monomial]
  have he : (∑ i ∈ Finset.Ico 1 p, ∑ j ∈ Finset.Ico 1 p,
      (if i + j < p then
        C (a ^ i * b ^ j / ((i : K) * (j : K))) * X ^ (i + j) else 0).eval z) =
      ∑ ij ∈ WPFiniteLogProduct.lowRect p,
        (a * z) ^ ij.1 * (b * z) ^ ij.2 / ((ij.1 : K) * (ij.2 : K)) := by
    simp only [WPFiniteLogProduct.lowRect, WPFiniteLogProduct.rect,
      Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp only [eval_mul, eval_C, eval_pow, eval_X, eval_zero]
    rw [pow_add, mul_pow, mul_pow]
    ring
  rw [he, ← WPFiniteLogProduct.low_reindex]
  simpa only [WPFiniteLogProduct.lowTriangle, Finset.sum_sigma] using
    (WPFiniteDReciprocity.T2_low_rows p (a * z) (b * z)).symm

private theorem endProduct_R_zero (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPFiniteField.R p (0 : K) = 0 := by
  unfold WPFiniteField.R
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
  simp only [zero_pow hj0, zero_div]

private theorem endProduct_ell_zero (p : ℕ) [Fact p.Prime] [CharP K p] :
    WPFiniteField.ell p (0 : K) = 0 := by
  unfold WPFiniteField.ell
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
  simp only [zero_pow hj0, zero_div]

private theorem endProduct_R_one (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    WPFiniteField.R p (1 : K) = 0 := by
  have he := WPFiniteField.R_weight_two_reflection (K := K) p (by omega) 0
  simpa only [zero_pow (by omega : p ≠ 0), zero_mul, sub_zero, one_pow,
    one_mul, endProduct_ell_zero, zero_pow (by decide : 2 ≠ 0), neg_zero,
    zero_div, zero_add] using he

/-- Finite reversal keeps every unit denominator in the full R carrier. -/
theorem endProduct_R_inversion (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : K) (ht : t ≠ 0) :
    WPFiniteField.R p t⁻¹ = (t ^ p)⁻¹ * WPFiniteField.R p t := by
  unfold WPFiniteField.R
  rw [← WPFiniteInversion.full_cutoff_reflection p
    (fun j => t⁻¹ ^ j / (j : K) ^ 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [inv_pow_sub₀ ht (Finset.mem_Ico.mp hj).2.le,
    WPFiniteField.reflected_denominator p j hj]
  simp only [neg_sq, div_eq_mul_inv]
  ring

private theorem endProduct_H2_zero_left (p : ℕ) [Fact p.Prime] [CharP K p] (b : K) :
    WPFiniteDReciprocity.H2 p (0 : K) b = 0 := by
  unfold WPFiniteDReciprocity.H2
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by have := (Finset.mem_Ico.mp hj).1; omega
  simp only [zero_pow hj0, zero_mul, zero_div]

private theorem endProduct_H2_zero_right (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) :
    WPFiniteDReciprocity.H2 p a (0 : K) = 0 := by
  unfold WPFiniteDReciprocity.H2
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : p - j ≠ 0 := by have := (Finset.mem_Ico.mp hj).2; omega
  simp only [zero_pow hj0, mul_zero, zero_div]

private theorem endProduct_H2_diagonal (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (a : K) : WPFiniteDReciprocity.H2 p a a = 0 := by
  by_cases ha : a = 0
  · rw [ha, endProduct_H2_zero_left]
  · rw [WPFiniteHomogeneousD.H2_scaled_R p a a ha,
      div_self ha, endProduct_R_one p hp, mul_zero]

private theorem endProduct_D_right_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) :
    WPFiniteLoop.D (p - 1) t 1 = WPFiniteField.R p (1 - t) := by
  rw [WPFiniteHomogeneousD.full_D_three_H2 p hp]
  simp only [sub_self, endProduct_H2_zero_right, zero_add]
  rw [WPFiniteHomogeneousD.H2_scaled_R p (1 - t) 1 one_ne_zero]
  simp only [one_pow, one_mul, div_one]

private theorem endProduct_H2_ratio (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) (ht : t ≠ 0) (ht1 : t ≠ 1) :
    WPFiniteDReciprocity.H2 p (-t) (1 - t) =
      -(t ^ p) * WPFiniteField.R p ((t - 1) / t) := by
  have h1t : (1 - t : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have hz : -t / (1 - t) ≠ 0 := div_ne_zero (neg_ne_zero.mpr ht) h1t
  have hi : (-t / (1 - t))⁻¹ = (t - 1) / t := by
    field_simp [ht, h1t]
    ring
  have he := endProduct_R_inversion p (-t / (1 - t)) hz
  rw [hi] at he
  have hri : WPFiniteField.R p (-t / (1 - t)) =
      (-t / (1 - t)) ^ p * WPFiniteField.R p ((t - 1) / t) := by
    rw [he]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero p hz), one_mul]
  rw [WPFiniteHomogeneousD.H2_scaled_R p (-t) (1 - t) h1t, hri]
  have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rw [div_pow, hodd.neg_pow]
  field_simp [pow_ne_zero p h1t]

private theorem endProduct_R_ratio (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) (ht : t ≠ 0) (ht1 : t ≠ 1) (htp : t ^ p = t) :
    t * WPFiniteField.R p ((t - 1) / t) =
      WPFiniteField.R p t - WPFiniteField.R p (1 - t) := by
  have h1t : (1 - t : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have h1tp : (1 - t : K) ^ p = 1 - t := by
    rw [sub_pow_char, one_pow, htp]
  have hitp : (t⁻¹ : K) ^ p = t⁻¹ := by rw [inv_pow, htp]
  have hw : 1 - t⁻¹ = (t - 1) / t := by field_simp [ht]
  have hwp : (1 - t⁻¹ : K) ^ p = 1 - t⁻¹ := by
    rw [sub_pow_char, one_pow, hitp]
  have ha := WPFiniteField.R_weight_two_reflection p (by omega) t
  have hb := WPFiniteField.R_weight_two_reflection p (by omega) t⁻¹
  rw [htp, h1tp] at ha
  rw [hitp, hwp, hw, endProduct_R_inversion p t ht,
    WPFiniteField.ell_inversion p t ht, htp] at hb
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have hh : (t - 1 : K) ≠ 0 := sub_ne_zero.mpr ht1
  linear_combination (norm := (field_simp [ht, hh, h2]; ring))
    (t ^ 2 / (t - 1)) * hb - (1 / (t - 1)) * ha

/-- Full-length unit shuffle, under the actual Frobenius hypothesis used at rational ends. -/
theorem endProduct_T2_rational_shuffles (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) (ht : t ≠ 0) (ht1 : t ≠ 1) (htp : t ^ p = t) :
    WPFiniteDReciprocity.T2 p t t = -2 * WPFiniteField.R p (1 - t) ∧
      WPFiniteDReciprocity.T2 p 1 t =
        WPFiniteField.R p t - WPFiniteField.R p (1 - t) := by
  have hr := endProduct_R_ratio p hp t ht ht1 htp
  have htt := WPFiniteHomogeneousD.full_D_three_H2 (K := K) p hp t t
  simp only [sub_self, endProduct_H2_zero_left, zero_sub, add_zero] at htt
  rw [endProduct_H2_ratio p hp t ht ht1, htp] at htt
  have h1t := WPFiniteHomogeneousD.full_D_three_H2 (K := K) p hp 1 t
  rw [endProduct_H2_diagonal p hp (1 - t), endProduct_H2_ratio p hp t ht ht1,
    WPFiniteHomogeneousD.H2_scaled_R p (t - 1) t ht, htp] at h1t
  constructor
  · unfold WPFiniteDReciprocity.T2
    rw [htt]
    linear_combination 2 * hr
  · unfold WPFiniteDReciprocity.T2
    rw [h1t, endProduct_D_right_one p hp, endProduct_R_one p hp]
    linear_combination 2 * hr

private theorem endProduct_T2_one_one (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : WPFiniteDReciprocity.T2 p (1 : K) 1 = 0 := by
  unfold WPFiniteDReciprocity.T2
  rw [endProduct_D_right_one p hp, sub_self, endProduct_R_zero,
    endProduct_R_one p hp]
  ring

private theorem endProduct_T2_symm (p : ℕ) [Fact p.Prime] [CharP K p] (a b : K) :
    WPFiniteDReciprocity.T2 p a b = WPFiniteDReciprocity.T2 p b a := by
  unfold WPFiniteDReciprocity.T2
  ring

/-- The four R letters introduced by the low shuffle reduce to the same literal R(16). -/
theorem endProduct_R_sixteen_reflection (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    WPFiniteField.R p (1 / 16 : K) = WPFiniteField.R p (16 : K) / 16 ∧
      WPFiniteField.R p (15 / 16 : K) =
        -(WPFiniteField.ell p (16 : K)) ^ 2 / 480 - WPFiniteField.R p (16 : K) / 240 ∧
      WPFiniteField.R p (-15 : K) =
        (WPFiniteField.ell p (16 : K)) ^ 2 / 30 + 16 * WPFiniteField.R p (16 : K) / 15 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have h15 : (15 : K) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h16 : (16 : K) ≠ 0 := by convert pow_ne_zero 4 h2 using 1; norm_num
  have h16p : (16 : K) ^ p = 16 := WPFiniteField.natCast_pow_char p 16
  have ha : (1 / 16 : K) ^ p = 1 / 16 := by rw [one_div, inv_pow, h16p]
  have hf15 : (15 : K) ^ p = 15 := by
    simpa only [Nat.cast_ofNat] using WPFiniteField.natCast_pow_char (K := K) p 15
  have h15p : (15 / 16 : K) ^ p = 15 / 16 := by
    rw [div_pow, hf15, h16p]
  have hm15p : (-15 : K) ^ p = -15 := by
    have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
    rw [hodd.neg_pow, hf15]
  have hr0 := endProduct_R_inversion p (16 : K) h16
  have hl := WPFiniteField.ell_inversion p (16 : K) h16
  rw [h16p] at hr0 hl
  have hr : WPFiniteField.R p (1 / 16 : K) = WPFiniteField.R p (16 : K) / 16 := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hr0
  have hxa : (1 - 1 / 16 : K) = 15 / 16 := by field_simp [h16]; ring
  have hxb : (1 - (16 : K)) = -15 := by ring
  have hfa := WPFiniteField.R_weight_two_reflection (K := K) p (by omega) (1 / 16)
  have hfb := WPFiniteField.R_weight_two_reflection (K := K) p (by omega) 16
  rw [ha, hxa, h15p, hr, show (1 / 16 : K) = (16 : K)⁻¹ by rw [one_div], hl] at hfa
  rw [h16p, hxb, hm15p] at hfb
  refine ⟨hr, ?_, ?_⟩
  · linear_combination (norm := (field_simp [h2, h3, h5, h15, h16, hu30, hu240, hu480]; ring))
      (16 / 15 : K) * hfa
  · linear_combination (norm := (field_simp [h2, h3, h5, h15, hu30]; ring))
      (-1 / 15 : K) * hfb

/-- Every low log-square slot is evaluated after the strict p cutoff. -/
theorem endProduct_low_log_four (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endProductLow p (((LP p : K[X]).comp (C (1 / 4 : K) * X)) ^ 2)).eval (1 / 4) =
      (WPFiniteField.ell p (16 : K)) ^ 2 / 240 + WPFiniteField.R p (16 : K) / 120 ∧
    (endProductLow p (((LP p : K[X]).comp (C (1 / 4 : K) * X)) *
      ((LP p).comp (C (4 : K) * X)))).eval (1 / 4) =
      (WPFiniteField.ell p (16 : K)) ^ 2 / 480 + WPFiniteField.R p (16 : K) / 15 ∧
    (endProductLow p (((LP p : K[X]).comp (C (1 / 4 : K) * X)) *
      ((LP p).comp (C (4 : K) * X)))).eval 4 =
      -(WPFiniteField.ell p (16 : K)) ^ 2 / 30 - WPFiniteField.R p (16 : K) / 15 ∧
    (endProductLow p (((LP p : K[X]).comp (C (4 : K) * X)) ^ 2)).eval 4 =
      -(WPFiniteField.ell p (16 : K)) ^ 2 / 15 - 32 * WPFiniteField.R p (16 : K) / 15 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h16 : (16 : K) ≠ 0 := by convert pow_ne_zero 4 h2 using 1; norm_num
  have h16one : (16 : K) ≠ 1 := by
    intro he
    have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 15
      (Finset.mem_Ico.mpr (by omega))
    apply h15
    calc (15 : K) = 16 - 1 := by ring
         _ = 0 := by rw [he, sub_self]
  have ha0 : (1 / 16 : K) ≠ 0 := one_div_ne_zero h16
  have ha1 : (1 / 16 : K) ≠ 1 := by
    intro he
    apply h16one
    have hh := congrArg (fun z : K => z * 16) he
    simpa only [one_div_mul_cancel h16, one_mul] using hh.symm
  have h16p : (16 : K) ^ p = 16 := WPFiniteField.natCast_pow_char p 16
  have hap : (1 / 16 : K) ^ p = 1 / 16 := by rw [one_div, inv_pow, h16p]
  obtain ⟨hsqa, hma⟩ := endProduct_T2_rational_shuffles p hp (1 / 16) ha0 ha1 hap
  obtain ⟨hsqb, hmb⟩ := endProduct_T2_rational_shuffles p hp 16 h16 h16one h16p
  obtain ⟨hRa, hR15, hRm15⟩ := endProduct_R_sixteen_reflection (K := K) p hp
  have haa : (1 / 4 : K) * (1 / 4) = 1 / 16 := by field_simp [h4, h16]; ring
  have hab : (1 / 4 : K) * 4 = 1 := one_div_mul_cancel h4
  have hba : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  have hbb : (4 : K) * 4 = 16 := by ring
  have haarg : (1 - 1 / 16 : K) = 15 / 16 := by field_simp [h16]; ring
  have hbarg : (1 - (16 : K)) = -15 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_two, endProduct_low_log_T2, haa, hsqa, haarg, hR15]
    field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
    ring
  · rw [endProduct_low_log_T2, haa, hba, endProduct_T2_symm, hma,
      hRa, haarg, hR15]
    field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
    ring
  · rw [endProduct_low_log_T2, hab, hbb, hmb, hbarg, hRm15]
    field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
    ring
  · rw [pow_two, endProduct_low_log_T2, hbb, hsqb, hbarg, hRm15]
    field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
    ring

/-- The original unit primitive is the same moving-H carrier at every point. -/
theorem endProduct_E_unitPrimitive (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z y : K) :
    unitPrimitive p (endProductE p : K[X]) z y =
      ActualKwFiniteHBridge.movingH p z y := by
  let N := (p - 1) / 2
  have hdeg : (endProductE p : K[X]).natDegree ≤ N :=
    (endProduct_E_degree (K := K) p hp).trans (by dsimp only [N]; omega)
  have hsub : Finset.range (N + 1) ⊆ Finset.range p := by
    intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (by dsimp only [N] at *; omega)
  have he : unitPrimitive p (endProductE p : K[X]) z y =
      ActualKwWeightedTrace.finiteH N (fun i => (endProductE p : K[X]).coeff i) z y := by
    let f (i : ℕ) : K := (endProductE p : K[X]).coeff i *
      ActualKwWeightedTrace.triangle i z y
    have hsum : (∑ i ∈ Finset.range (N + 1), f i) = ∑ i ∈ Finset.range p, f i := by
      apply Finset.sum_subset hsub
      intro i hi hnot
      have hiN : N < i := by
        have hn : ¬i < N + 1 := by simpa only [Finset.mem_range] using hnot
        omega
      dsimp only [f]
      rw [coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hiN), zero_mul]
    have hsplit : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hf0 : f 0 = 0 := by simp [f, ActualKwWeightedTrace.triangle]
    change (∑ i ∈ Finset.Ico 1 p, f i) = ∑ i ∈ Finset.range (N + 1), f i
    rw [hsum, hsplit, Finset.sum_insert (by simp : 0 ∉ Finset.Ico 1 p), hf0, zero_add]
  rw [he]
  simpa only [N, endProductE, ActualKwFiniteHBridge.movingH] using
    ActualKwFiniteHBridge.finiteH_movingEven_D (K := K) p hp z y

noncomputable def endProductEBlock (p : ℕ) : K[X] :=
  -C (2 / 45 : K) *
    (C (35 : K) * (LP p).comp (C (1 / 4 : K) * X) -
      C (5 : K) * (LP p).comp (C (4 : K) * X)) * endProductE p

noncomputable def endProductLogBlock (p : ℕ) : K[X] :=
  -C (1 / 45 : K) *
    (C (35 : K) * ((LP p).comp (C (1 / 4 : K) * X)) ^ 2 -
      C (40 : K) * (LP p).comp (C (1 / 4 : K) * X) * (LP p).comp (C (4 : K) * X) +
      C (5 : K) * ((LP p).comp (C (4 : K) * X)) ^ 2)

noncomputable def endProductLinearBlock (p : ℕ) : K[X] :=
  C (2 * WPFiniteNC122.q p / 45 : K) *
    (C (35 : K) * (LP p).comp (C (1 / 4 : K) * X) -
      C (5 : K) * (LP p).comp (C (4 : K) * X))

private theorem endProductHigh_sub (p : ℕ) (P Q : K[X]) :
    endProductHigh p (P - Q) = endProductHigh p P - endProductHigh p Q := by
  ext j
  simp only [endProductHigh_coeff, coeff_sub]
  split_ifs <;> ring

private theorem endProduct_W1_E (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (endKernelW1 p : K[X]) =
      -C (4 / 15 : K) * endProductE p - C (2 / 15 : K) *
        ((LP p).comp (C (1 / 4 : K) * X) - (LP p).comp (C (4 : K) * X)) +
      C (4 * WPFiniteNC122.q p / 15) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have hc : (4 / 5 : K) * (1 / 3) = 4 / 15 := by field_simp [h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]; ring
  unfold endKernelW1 Dstar endProductE
  rw [show C (4 / 5 : K) * (-C (1 / 3 : K) *
      (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate) =
      -C ((4 / 5 : K) * (1 / 3)) *
        (WPFiniteWSource.deltaE p).comp WPFiniteWSource.squaredCoordinate by
      rw [map_mul]; ring, hc]

/-- The exact first end product splits into its e, logarithm-square and linear sources. -/
theorem endProduct_first_product_blocks (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endProductK0 p : K[X]) * endKernelW1 p =
      endProductEBlock p + endProductLogBlock p + endProductLinearBlock p := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have hc : -(1 / 6 : K) * (4 / 15) + 2 / 45 = 0 ∧
      -(1 / 6 : K) * (2 / 15) + 1 / 45 = 0 ∧
      (1 / 6 : K) * (4 * WPFiniteNC122.q p / 15) - 2 * WPFiniteNC122.q p / 45 = 0 := by
    refine ⟨?_, ?_, ?_⟩ <;> field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480] <;> ring
  let A : K[X] := (LP p).comp (C (1 / 4 : K) * X)
  let B : K[X] := (LP p).comp (C (4 : K) * X)
  have hd : (endProductK0 p : K[X]) * endKernelW1 p -
      (endProductEBlock p + endProductLogBlock p + endProductLinearBlock p) =
      C (-(1 / 6 : K) * (4 / 15) + 2 / 45) * (C 35 * A - C 5 * B) * endProductE p +
      C (-(1 / 6 : K) * (2 / 15) + 1 / 45) * (C 35 * A ^ 2 - C 40 * A * B + C 5 * B ^ 2) +
      C ((1 / 6 : K) * (4 * WPFiniteNC122.q p / 15) - 2 * WPFiniteNC122.q p / 45) *
        (C 35 * A - C 5 * B) := by
    rw [endProduct_W1_E p hp]
    simp only [endProductK0, endProductEBlock, endProductLogBlock, endProductLinearBlock,
      A, B, map_add, map_sub, map_neg, map_mul]
    rw [show (C (40 : K) : K[X]) = C (35 : K) + C (5 : K) by
      rw [← map_add]; congr 1; ring]
    ring
  rw [hc.1, hc.2.1, hc.2.2] at hd
  simp only [map_zero, zero_mul, zero_add] at hd
  exact sub_eq_zero.mp hd

private theorem endProduct_log_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    ((LP p : K[X]).comp (C (1 / 4 : K) * X)).eval (1 / 4) =
      -WPFiniteField.ell p (16 : K) / 16 ∧
    ((LP p : K[X]).comp (C (4 : K) * X)).eval (1 / 4) = 0 ∧
    ((LP p : K[X]).comp (C (1 / 4 : K) * X)).eval 4 = 0 ∧
    ((LP p : K[X]).comp (C (4 : K) * X)).eval 4 = WPFiniteField.ell p (16 : K) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h16 : (16 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 16
    (Finset.mem_Ico.mpr (by omega))
  have h16p : (16 : K) ^ p = 16 := WPFiniteField.natCast_pow_char p 16
  have hi := WPFiniteField.ell_inversion p (16 : K) h16
  rw [h16p] at hi
  have h1 : WPFiniteField.ell p (1 : K) = 0 :=
    (WPFiniteCubicJ.rational_ell_sources (K := K) p hp).1
  have haa : (1 / 4 : K) * (1 / 4) = 1 / 16 := by field_simp [h4, h16]; ring
  have hab : (4 : K) * (1 / 4) = 1 := mul_one_div_cancel h4
  have hba : (1 / 4 : K) * 4 = 1 := one_div_mul_cancel h4
  have hbb : (4 : K) * 4 = 16 := by ring
  simp only [eval_comp, eval_mul, eval_C, eval_X, haa, hab, hba, hbb, LP_eval_eq,
    h1, show (1 / 16 : K) = (16 : K)⁻¹ by rw [one_div], hi]
  refine ⟨?_, by simp only, by simp only, by simp only⟩
  ring

/-- The e contraction retains the inclusive p slot in all four original products. -/
theorem endProduct_EBlock_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    8 * (endProductLow p (endProductEBlock p : K[X]) -
      C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductEBlock p) -
        C (2 / 5 : K) * endProductHigh p (endProductK1 p * endProductE p)).eval 4 =
      -(94 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) (1 / 4) -
        (47 / 45 : K) * ActualKwFiniteHBridge.movingH p 4 (1 / 4) +
        (103 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) 4 +
        (103 / 90 : K) * ActualKwFiniteHBridge.movingH p 4 4 +
        WPFiniteField.ell p (16 : K) *
          (14 * (endProductE p : K[X]).eval (1 / 4) + (endProductE p).eval 4) / 18 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  let A : K[X] := (LP p).comp (C (1 / 4 : K) * X)
  let B : K[X] := (LP p).comp (C (4 : K) * X)
  have he : (endProductEBlock p : K[X]) =
      -C (2 / 45 : K) * (C 35 * (endProductE p * A) - C 5 * (endProductE p * B)) := by
    dsimp only [endProductEBlock, A, B]
    ring
  have hk : (endProductK1 p : K[X]) * endProductE p =
      C (1 / 6 : K) * (C 92 * (endProductE p * A) - C (29 / 4 : K) * (endProductE p * B)) := by
    dsimp only [endProductK1, A, B]
    simp only [div_eq_mul_inv, map_mul, map_one]
    ring
  obtain ⟨haa, hab, hba, hbb⟩ := endProduct_E_log_high_four (K := K) p hp
  obtain ⟨hAa, hBa, hAb, hBb⟩ := endProduct_log_ends (K := K) p hp
  simp only [endProductLow]
  rw [he, hk]
  simp only [← map_neg, endProductHigh_C_mul, endProductHigh_sub,
    eval_sub, eval_mul, eval_C, A, B, haa, hab, hba, hbb, hAa, hBa, hAb, hBb,
    endProduct_E_unitPrimitive p hp]
  field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
  ring

/-- The original logarithm-square part contracts to R(16) after its strict low shuffle. -/
theorem endProduct_LogBlock_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    8 * (endProductLow p (endProductLogBlock p : K[X])).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductLogBlock p)).eval 4 =
      -(WPFiniteField.ell p (16 : K)) ^ 2 / 60 + 7 * WPFiniteField.R p (16 : K) / 15 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have hAone : (endProductLow p (((LP p : K[X]).comp (C (1 / 4 : K) * X)) ^ 2)).eval 4 = 0 := by
    rw [pow_two, endProduct_low_log_T2, one_div_mul_cancel h4, endProduct_T2_one_one p hp]
  have hBone : (endProductLow p (((LP p : K[X]).comp (C (4 : K) * X)) ^ 2)).eval (1 / 4) = 0 := by
    rw [pow_two, endProduct_low_log_T2, mul_one_div_cancel h4, endProduct_T2_one_one p hp]
  obtain ⟨hsqa, hma, hmb, hsqb⟩ := endProduct_low_log_four (K := K) p hp
  have hAB : C (40 : K) * (LP p).comp (C (1 / 4 : K) * X) *
      (LP p).comp (C (4 : K) * X) = C (40 : K) *
        ((LP p).comp (C (1 / 4 : K) * X) * (LP p).comp (C (4 : K) * X)) := by ring
  simp only [endProductLogBlock, ← map_neg, hAB,
    endProductLow_C_mul, endProductLow_add, endProductLow_sub,
    eval_mul, eval_C, eval_add, eval_sub, hsqa, hma, hmb, hsqb, hAone, hBone]
  field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
  ring

/-- No p tail occurs in the linear source; its two literal endpoint logs are retained. -/
theorem endProduct_LinearBlock_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    8 * (endProductLow p (endProductLinearBlock p : K[X])).eval (1 / 4) +
      (1 / 4 : K) * (endProductLow p (endProductLinearBlock p)).eval 4 =
      -5 * WPFiniteNC122.q p * WPFiniteField.ell p (16 : K) / 6 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have hd : (endProductLinearBlock p : K[X]).natDegree < p := by
    apply (natDegree_C_mul_le _ _).trans_lt
    apply (natDegree_sub_le _ _).trans_lt
    apply max_lt
    · exact (natDegree_C_mul_le _ _).trans_lt (by
        have := endProduct_scaled_log_degree (K := K) p (1 / 4); omega)
    · exact (natDegree_C_mul_le _ _).trans_lt (by
        have := endProduct_scaled_log_degree (K := K) p 4; omega)
  have hz := endProductHigh_small p (endProductLinearBlock p : K[X]) hd
  obtain ⟨hAa, hBa, hAb, hBb⟩ := endProduct_log_ends (K := K) p hp
  simp only [endProductLow, hz, sub_zero]
  simp only [endProductLinearBlock, eval_mul, eval_C, eval_sub, hAa, hBa, hAb, hBb]
  field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
  ring

/-- The actual original end product is fully contracted; no low or high product remains. -/
theorem endProduct_actual_density_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    -originPole ((LaurentPolynomial.C (33 : K) - LaurentPolynomial.C (12 : K) * T 1) *
      (literalKB p * endKernelChi0 p)) +
      originPole ((LaurentPolynomial.C (31 * WPFiniteNC122.q p) -
        LaurentPolynomial.C (4 * WPFiniteNC122.q p) * T 1) * literalKB p) =
      -(94 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) (1 / 4) -
        (47 / 45 : K) * ActualKwFiniteHBridge.movingH p 4 (1 / 4) +
        (103 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) 4 +
        (103 / 90 : K) * ActualKwFiniteHBridge.movingH p 4 4 +
        WPFiniteField.ell p (16 : K) *
          (14 * (endProductE p : K[X]).eval (1 / 4) + (endProductE p).eval 4) / 18 -
        (WPFiniteField.ell p (16 : K)) ^ 2 / 60 + 7 * WPFiniteField.R p (16 : K) / 15 -
        5 * WPFiniteNC122.q p * WPFiniteField.ell p (16 : K) / 6 := by
  rw [endProduct_actual_density_cancellation p hp, endProduct_first_product_blocks p hp,
    endProductLow_add, endProductLow_add]
  have he := endProduct_EBlock_contraction (K := K) p hp
  have hl := endProduct_LogBlock_contraction (K := K) p hp
  have ht := endProduct_LinearBlock_contraction (K := K) p hp
  simp only [eval_sub, eval_add, eval_mul, eval_C] at he hl ht ⊢
  linear_combination he + hl + ht

private theorem endProduct_E_ends (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    (endProductE p : K[X]).eval (1 / 4) = -3 * WPFiniteNC122.q p - WPFiniteNC122.h p / 2 ∧
      (endProductE p : K[X]).eval 4 = 3 * WPFiniteNC122.q p + WPFiniteNC122.h p := by
  obtain ⟨ha, hb⟩ := Dstar_endpoints (K := K) p hp
  change (-C (1 / 3 : K) * endProductE p).eval (1 / 4) = _ at ha
  change (-C (1 / 3 : K) * endProductE p).eval 4 = _ at hb
  simp only [eval_neg, eval_mul, eval_C] at ha hb
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by ring]
    exact mul_ne_zero h2 h3
  constructor
  · linear_combination (norm := (field_simp [h2, h3, h6]; ring)) (-3 : K) * ha
  · linear_combination (norm := (field_simp [h3]; ring)) (-3 : K) * hb

/-- The four genuine fifth/rational H endpoints contract to the existing G(1/5). -/
theorem endProduct_four_H_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    -(94 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) (1 / 4) -
      (47 / 45 : K) * ActualKwFiniteHBridge.movingH p 4 (1 / 4) +
      (103 / 45 : K) * ActualKwFiniteHBridge.movingH p (1 / 4) 4 +
      (103 / 90 : K) * ActualKwFiniteHBridge.movingH p 4 4 =
      -originalG p (1 / 5 : K) / 20 + WPFiniteField.R p (-2 : K) / 10 -
        97 * WPFiniteNC122.q p ^ 2 / 15 +
        10 * WPFiniteNC122.q p * ActualRationalSignRows.q3 p -
        15 * ActualRationalSignRows.q3 p ^ 2 / 4 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  have haa := movingH_aa p u hu h4 h5
  have hba := movingH_ba p u hu h4 h5
  have hab := movingH_ab p u hu h4 h5
  have hbb := movingH_bb p u hu h2 h5
  have hHaa : ActualKwFiniteHBridge.movingH p (1 / 4 : K) (1 / 4) =
      (WPFiniteLoop.S p 1 1 - WPFiniteLoop.S p (1 / 2) (1 / 2) - WPFiniteLoop.A p u) / 2 := by
    linear_combination (norm := (field_simp [h2]; ring)) (1 / 2 : K) * haa
  have hHba : ActualKwFiniteHBridge.movingH p (4 : K) (1 / 4) =
      (WPFiniteLoop.S p 1 2 - WPFiniteLoop.S p (1 / 2) 1 - WPFiniteLoop.B p u) / 2 := by
    linear_combination (norm := (field_simp [h2]; ring)) (1 / 2 : K) * hba
  have hHab : ActualKwFiniteHBridge.movingH p (1 / 4 : K) 4 =
      (WPFiniteLoop.S p 2 1 - WPFiniteLoop.S p 1 (1 / 2) - WPFiniteLoop.A p u) / 2 := by
    linear_combination (norm := (field_simp [h2]; ring)) (1 / 2 : K) * hab
  have hHbb : ActualKwFiniteHBridge.movingH p (4 : K) 4 =
      (WPFiniteLoop.S p 2 2 - WPFiniteLoop.S p 1 1 - WPFiniteLoop.B p u) / 2 := by
    linear_combination (norm := (field_simp [h2]; ring)) (1 / 2 : K) * hbb
  have hG : originalG p (1 / 5 : K) = WPFiniteLoop.B p u + 2 * WPFiniteLoop.A p u := by
    rw [← hu, originalG_square]
  rw [hHaa, hHba, hHab, hHbb, hG,
    ActualKwRationalRowAttachment.native_S_one_one p hp,
    ActualKwRationalRowAttachment.native_S_half_half p hp,
    ActualKwRationalRowAttachment.native_S_one_two p hp,
    ActualKwRationalRowAttachment.native_S_half_one p hp,
    ActualKwRationalRowAttachment.native_S_two_one p hp,
    ActualKwRationalRowAttachment.native_S_one_half p hp,
    ActualKwRationalRowAttachment.native_S_two_two p hp]
  dsimp only [ActualRationalSignRows.q2, ActualRationalSignRows.q3, WPFiniteNC122.q]
  field_simp [h2, h3, h4, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
  ring

/-- The original chi0, Lambda_end, and derivative part of NC123b; no component value is assigned. -/
noncomputable def endProductActualGB (p : ℕ) [Fact p.Prime] [CharP K p] (u : K) : K :=
  let chi0 := WPFiniteZSource.P p u - LaurentPolynomial.C (1 / 3 : K) *
    ((actualAK p : K[X]).toLaurent + LaurentPolynomial.C (WPFiniteNC122.h p));
  -originPole ((LaurentPolynomial.C (33 : K) - LaurentPolynomial.C (12 : K) * T 1) *
      (literalKB p * chi0)) +
    originPole ((LaurentPolynomial.C (31 * WPFiniteNC122.q p) -
      LaurentPolynomial.C (4 * WPFiniteNC122.q p) * T 1) * literalKB p) -
    2 * WPFiniteNC122.h p * (literalKB p * WPFiniteLaurentDifferential.D chi0).coeff (-1)

/-- SB107i for the complete actual source, with the original chi0 and Lambda retained. -/
theorem endProduct_actual_GB_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    endProductActualGB p u =
      -originalG p (1 / 5 : K) / 20 + WPFiniteField.R p (-2 : K) / 10 +
      7 * WPFiniteField.R p (16 : K) / 15 + 313 * WPFiniteNC122.q p ^ 2 / 3 -
      27 * WPFiniteNC122.q p * ActualRationalSignRows.q3 p / 10 -
      13 * WPFiniteNC122.q p * (WPFiniteInversion.integerFermatQuotient p 5 : K) -
      15 * ActualRationalSignRows.q3 p * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
      15 * (WPFiniteInversion.integerFermatQuotient p 5 : K) ^ 2 / 4 +
      2 * WPFiniteNC122.q p * WPFifthEntropy.C p u / 5 +
      3 * ActualRationalSignRows.q3 p * WPFifthEntropy.C p u / 10 := by
  dsimp only [endProductActualGB]
  simp only [actual_P_endKernel_source p hp u hu]
  rw [endProduct_actual_density_value p hp, endKernel_derivative_fifth p hp u hu,
    endProduct_four_H_value p hp u hu]
  obtain ⟨hea, heb⟩ := endProduct_E_ends (K := K) p hp
  rw [hea, heb]
  have hl := (finiteLog_c_ordered (K := K) p hp).2
  change WPFiniteField.ell p (16 : K) = _ at hl
  rw [hl]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480⟩ := endProduct_denominator_units (K := K) p hp
  dsimp only [WPFiniteNC122.h, WPFiniteNC122.q, ActualRationalSignRows.q3]
  field_simp [h2, h3, h5, hu4, hu6, hu10, hu12, hu15, hu16, hu18, hu20, hu30, hu40, hu45, hu60, hu90, hu120, hu240, hu480]
  ring

/-- The literal R0 origin term is retained until the whole kernel proves its residue zero. -/
theorem endProduct_actual_GB_with_origin (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u r0 : K) (hu : u ^ 2 = 1 / 5) :
    endProductActualGB p u +
      (literalKB p * (LaurentPolynomial.C (r0 - WPFiniteNC122.h p) * T (-1))).coeff (-1) =
      -originalG p (1 / 5 : K) / 20 + WPFiniteField.R p (-2 : K) / 10 +
      7 * WPFiniteField.R p (16 : K) / 15 + 313 * WPFiniteNC122.q p ^ 2 / 3 -
      27 * WPFiniteNC122.q p * ActualRationalSignRows.q3 p / 10 -
      13 * WPFiniteNC122.q p * (WPFiniteInversion.integerFermatQuotient p 5 : K) -
      15 * ActualRationalSignRows.q3 p * (WPFiniteInversion.integerFermatQuotient p 5 : K) / 2 -
      15 * (WPFiniteInversion.integerFermatQuotient p 5 : K) ^ 2 / 4 +
      2 * WPFiniteNC122.q p * WPFifthEntropy.C p u / 5 +
      3 * ActualRationalSignRows.q3 p * WPFifthEntropy.C p u / 10 := by
  rw [literalKB_simple_pole_zero, add_zero, endProduct_actual_GB_value p hp u hu]

end WPFieldAssembly.ActualBpairContraction
