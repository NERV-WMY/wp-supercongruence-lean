import WPFieldAssembly.ActualFirstGreen
import WPFiniteCubicJ
import WPActualFieldPrimitive
import WPFieldAssembly.GreenLaurentOperators

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial
namespace WPFieldAssembly.ActualGreenResidue
open GreenLaurentOperators
variable {K : Type*} [Field K]

private theorem twice_EP_eval (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (t : K) :
    2 * (WPFiniteKSource.EP p : K[X]).eval t =
      WPFiniteField.ell p t + WPFiniteField.ell p (-t) := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h2
  simp only [WPFiniteKSource.EP, eval_mul, eval_C, eval_add, eval_comp,
    eval_neg, eval_X, WPFiniteAffineLog.LP_eval_eq]
  field_simp [h2]

/-- The finite endpoint relation uses integer Fermat quotients via rational_ell_sources. -/
theorem deltaE_weighted_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    2 * (WPFiniteWSource.deltaE p : K[X]).eval (1 / 4) +
      (WPFiniteWSource.deltaE p : K[X]).eval 1 = -3 * WPFiniteNC122.q p := by
  have h2 := WPFiniteField.denominator_ne_zero (K := K) p 2
    (Finset.mem_Ico.mpr (by omega))
  have hhalf : (1 / 2 : K) ^ 2 = 1 / 4 := by field_simp [h2]; ring
  have htwohalf : (2 : K) * (1 / 2) = 1 := mul_one_div_cancel h2
  have ha := congrArg (fun Q : K[X] => Q.eval (1 / 2))
    (WPFiniteWSource.deltaE_square (K := K) p hp)
  have hb := congrArg (fun Q : K[X] => Q.eval 1)
    (WPFiniteWSource.deltaE_square (K := K) p hp)
  simp only [eval_comp, eval_pow, eval_X, eval_sub, eval_mul, eval_ofNat,
    hhalf, htwohalf, one_pow, mul_one] at ha hb
  obtain ⟨h1, hn1, he2, hen2, hh, hnh⟩ :=
    WPFiniteCubicJ.rational_ell_sources (K := K) p hp
  have hE1 := twice_EP_eval (K := K) p hp 1
  have hE2 := twice_EP_eval (K := K) p hp 2
  have hEh := twice_EP_eval (K := K) p hp (1 / 2)
  apply mul_left_cancel₀ h2
  linear_combination 4 * ha + 2 * hb + hE1 + hE2 - 2 * hEh +
    h1 + hn1 + he2 + hen2 - hh - hnh

/-- The complete positive phase of universal P has zero middle residue. -/
theorem A_weighted_endpoints (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u ^ 2 = 1 / 5) :
    2 * (WPFiniteABSourceTail.A p (WPFiniteWSource.W p) u).eval (1 / 4) +
      (WPFiniteABSourceTail.A p (WPFiniteWSource.W p) u).eval 4 = 0 := by
  have h4 := WPFiniteField.denominator_ne_zero (K := K) p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 := WPFiniteField.denominator_ne_zero (K := K) p 5
    (Finset.mem_Ico.mpr (by omega))
  norm_num only [Nat.cast_ofNat] at h4 h5
  have hsa : (WPFiniteWSource.squaredCoordinate : K[X]).eval (1 / 4) = 1 / 4 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C,
      eval_add, eval_X, eval_one]
    field_simp [h4, h5]; ring
  have hsb : (WPFiniteWSource.squaredCoordinate : K[X]).eval 4 = 1 := by
    simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C,
      eval_add, eval_X, eval_one]
    field_simp [h5]; ring
  rw [WPFinitePSource.A_literal_even_difference (K := K) p hp u hu]
  simp only [eval_mul, eval_C, eval_add, eval_comp, hsa, hsb]
  have hδ := deltaE_weighted_endpoints (K := K) p hp
  linear_combination (-4 / 15 : K) * hδ

/-- The actual literal source, before choosing a Green primitive, has zero p-1 coefficient. -/
theorem literal_Peta_middle_zero (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (WPActualFieldPrimitive.literalFieldPeta p hp).coeff ((p : ℤ) - 1) = 0 := by
  rw [WPActualFieldPrimitive.literalFieldPeta, WPPIntegralReduction.reduceLaurent_coeff]
  simpa only [WPActualEtaPrimitive.actualResidue, one_mul] using
    (WPActualResidueVanishing.literal_three_residues_zero p hp).2.1

private theorem LP_scaled_degree (p : ℕ) (c : K) :
    ((WPFiniteAffineLog.LP p : K[X]).comp (Polynomial.C c*X)).natDegree ≤ p-1 := by
  have hlin : (Polynomial.C c*X : K[X]).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  exact natDegree_comp_le.trans (calc
    (WPFiniteAffineLog.LP p : K[X]).natDegree * (Polynomial.C c*X).natDegree ≤
        (p-1)*1 := Nat.mul_le_mul (WPFiniteAffineLog.LP_natDegree_le p) hlin
    _ = p-1 := Nat.mul_one _)

theorem P_middle_negative_degrees (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (WPFiniteABSourceTail.B0 p (WPFiniteWSource.W p) u).natDegree < p ∧
      (WPFinitePSource.Cminus p u).natDegree < p := by
  have hw := WPFiniteWSource.W_degree (K := K) p hp
  have hw' : (WPFiniteWSource.W p : K[X]).natDegree ≤ p-1 := by omega
  have hc (c : K) : (Polynomial.C c : K[X]).natDegree ≤ p-1 := by simp
  have hm (c : K) : (Polynomial.C c*(WPFiniteWSource.W p : K[X])).natDegree ≤ p-1 :=
    (natDegree_C_mul_le _ _).trans hw'
  have ht := WPFiniteABSourceTail.logTrace_degree (K := K) p
  have hd : (WPFinitePSource.logDifference p : K[X]).natDegree ≤ p-1 := by
    unfold WPFinitePSource.logDifference
    exact (natDegree_sub_le _ _).trans (max_le
      (LP_scaled_degree p 4) (LP_scaled_degree p (1/4)))
  constructor
  · apply lt_of_le_of_lt _ (show p-1 < p by omega)
    unfold WPFiniteABSourceTail.B0 WPFiniteABSourceTail.Bpoly
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le (hc _) (hm _)))
      ((natDegree_C_mul_le _ _).trans ht))
  · apply lt_of_le_of_lt _ (show p-1 < p by omega)
    unfold WPFinitePSource.Cminus
    exact (natDegree_add_le _ _).trans (max_le
      ((natDegree_sub_le _ _).trans (max_le (hc _) (hm _)))
      ((natDegree_C_mul_le _ _).trans hd))

theorem P_DD_middle (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u a ai : K) :
    (DD a ai (WPFiniteZSource.P p u)).coeff ((p : ℤ)-1) =
      (WPFiniteABSourceTail.A p (WPFiniteWSource.W p) u).eval a := by
  obtain ⟨hb,hc⟩ := P_middle_negative_degrees (K := K) p hp u
  have hB := DD_polynomial_phase_zero p (by omega) a ai 0
    (WPFiniteABSourceTail.B0 p (WPFiniteWSource.W p) u) (by omega)
  have hC := DD_polynomial_phase_zero p (by omega) a ai (-(p : ℤ))
    (WPFinitePSource.Cminus p u) (by omega)
  simp only [T_zero,one_mul] at hB
  rw [WPFiniteZSource.P, map_add, map_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    DD_positive_phase_middle p (by omega), hB, hC]
  ring

theorem finite_P_middle_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) (hu : u^2=1/5) :
    (weightedDD (WPFiniteZSource.P p u)).coeff ((p : ℤ)-1) = 0 := by
  simp only [weightedDD, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    GreenLaurentOperators.C_mul_coeff, P_DD_middle p hp]
  exact A_weighted_endpoints p hp u hu

theorem derivative_middle_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (G : K[T;T⁻¹]) :
    (WPFiniteLaurentDifferential.D G).coeff ((p : ℤ)-1)=0 := by
  rw [WPFiniteLaurentDifferential.D_coeff, sub_add_cancel]
  simp only [Int.cast_natCast, CharP.cast_eq_zero, zero_mul]

end WPFieldAssembly.ActualGreenResidue
