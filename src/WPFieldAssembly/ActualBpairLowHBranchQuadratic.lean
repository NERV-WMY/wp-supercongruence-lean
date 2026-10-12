import WPFieldAssembly.ActualBpairLowHBranchTail

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- These remain literal whole-source residues; no scalar is assigned to either functional. -/
noncomputable def lowHBranchJ0 (p : ℕ) (H : K[X]) : K :=
  ((lowHBranchYQuotient H).toLaurent * Dsym p).coeff (-1)

noncomputable def lowHBranchJs (p : ℕ) (H : K[X]) : K :=
  ((lowHBranchYQuotient H).toLaurent * Dsym p *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)).coeff (-1)

theorem lowH_branch_square_derivative_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * Dsym p * D (Dsym p) =
      LaurentPolynomial.C (5 / 2 : K) * (lowHBranchYQuotient H).toLaurent * Dsym p *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        (T (-(((p - 1) / 2 : ℕ) : ℤ)) - 1) := by
  have he := Dsym_cleared_source (K := K) p hp
  rw [lowHBranchYQuotient_source H h0, map_mul]
  linear_combination (lowHBranchYQuotient H).toLaurent * Dsym p * he

/-- The full reciprocal branch term vanishes before the remaining Js functional is selected. -/
theorem lowH_branch_square_derivative_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    ((lowHCubicY H).toLaurent * Dsym p * D (Dsym p)).coeff (-1) =
      -(5 / 2 : K) * lowHBranchJs p H := by
  rw [lowH_branch_square_derivative_source p hp H h0]
  rw [show LaurentPolynomial.C (5 / 2 : K) * (lowHBranchYQuotient H).toLaurent * Dsym p *
      WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (T (-(((p - 1) / 2 : ℕ) : ℤ)) - 1) =
      LaurentPolynomial.C (5 / 2 : K) *
        ((lowHBranchYQuotient H).toLaurent * Dsym p *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
          T (-(((p - 1) / 2 : ℕ) : ℤ)) -
        (lowHBranchYQuotient H).toLaurent * Dsym p *
          WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) by ring]
  rw [C_mul_coeff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    lowH_branch_reciprocal_residue_zero p hp H hH]
  unfold lowHBranchJs
  ring

theorem lowH_branch_Dstar_derivative_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    (lowHCubicY H).toLaurent * Dsym p * D (Dstar p).toLaurent =
      LaurentPolynomial.C (5 / 2 : K) *
        ((lowHBranchYQuotient H).toLaurent * Dsym p -
          (lowHBranchYQuotient H).toLaurent * Dsym p *
            WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
  have he := congrArg (fun Q : K[X] => Q.toLaurent) (Dstar_cleared_source (K := K) p hp)
  simp only [map_mul, map_sub, map_pow, map_one, Polynomial.toLaurent_C, ← D_toLaurent] at he
  rw [lowHBranchYQuotient_source H h0, map_mul]
  linear_combination (lowHBranchYQuotient H).toLaurent * Dsym p * he

theorem lowH_branch_Dstar_derivative_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    ((lowHCubicY H).toLaurent * Dsym p * D (Dstar p).toLaurent).coeff (-1) =
      (5 / 2 : K) * (lowHBranchJ0 p H - lowHBranchJs p H) := by
  rw [lowH_branch_Dstar_derivative_source p hp H h0, C_mul_coeff,
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  rfl

theorem lowH_branch_plain_square_derivative_residue (p : ℕ) (H : K[X]) :
    ((lowHCubicY H).toLaurent * (Dstar p).toLaurent * D (Dstar p).toLaurent).coeff (-1) = 0 := by
  rw [D_toLaurent, ← map_mul, ← map_mul]
  exact WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))

/-- The whole retained quadratic combination keeps J0 until its actual D-linear cancellation. -/
theorem lowH_branch_quadratic_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    (LaurentPolynomial.C (166 / 25 : K) *
        ((lowHCubicY H).toLaurent * Dsym p * D (Dsym p)) -
      LaurentPolynomial.C (88 / 5 : K) *
        ((lowHCubicY H).toLaurent * Dsym p * D (Dstar p).toLaurent) +
      LaurentPolynomial.C (274 / 25 : K) *
        ((lowHCubicY H).toLaurent * (Dstar p).toLaurent * D (Dstar p).toLaurent)).coeff (-1) =
      (137 / 5 : K) * lowHBranchJs p H - 44 * lowHBranchJ0 p H := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h25 : (25 : K) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, C_mul_coeff,
    lowH_branch_square_derivative_residue p hp H hH h0,
    lowH_branch_Dstar_derivative_residue p hp H h0,
    lowH_branch_plain_square_derivative_residue, mul_zero, add_zero]
  field_simp [h2, h5, h25]
  ring

private theorem lowH_two_frobenius_phases_zero (p : ℕ) (F : K[T;T⁻¹])
    (hu : Above F ((p : ℤ) - 2)) (hl : Above (invert F) ((p : ℤ) - 2)) :
    (T (p : ℤ) * F).coeff (-1) = 0 ∧ (T (-(p : ℤ)) * F).coeff (-1) = 0 := by
  have hpos := WPFiniteJCarrier.shifted_coeff (1 : K) (p : ℤ) (-1) F
  have hneg := WPFiniteJCarrier.shifted_coeff (1 : K) (-(p : ℤ)) (-1) F
  simp only [map_one, one_mul] at hpos hneg
  constructor
  · rw [hpos]
    have he := hl ((p : ℤ) + 1) (by omega)
    rw [invert_apply] at he
    convert he using 1; ring
  · rw [hneg]
    exact hu _ (by omega)

private theorem lowH_quadratic_source_bounds (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    Above ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent)
        ((p : ℤ) - 2) ∧
      Above (invert ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent))
        ((p : ℤ) - 2) ∧
      Above ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent))
        ((p : ℤ) - 2) ∧
      Above (invert ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent)))
        ((p : ℤ) - 2) := by
  let N := (p - 1) / 2
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  have hY : Above (lowHCubicY H).toLaurent (N : ℤ) := by
    apply Above_toLaurent
    have hy := lowHCubicY_degree (p / 6) H hH
    have hb := lowH_prime_six_band p hp
    omega
  have hD : Above (Dstar p : K[X]).toLaurent ((N : ℤ) - 1) := by
    have he := Above_toLaurent (Dstar p : K[X]) (N - 1) (Dstar_degree p hp)
    simpa only [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] using he
  have hiD : Above (invert (Dstar p : K[X]).toLaurent) 0 := Above_invert_toLaurent _
  have hiY : Above (invert (lowHCubicY H).toLaurent) 0 := Above_invert_toLaurent _
  have hiDP : Above (invert (D (Dstar p : K[X]).toLaurent)) 1 := by
    intro j hj
    rw [invert_apply, D_coeff]
    rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)), mul_zero]
  have hiDiP : Above (invert (D (invert (Dstar p : K[X]).toLaurent))) (N : ℤ) := by
    intro j hj
    rw [invert_apply, D_coeff, invert_apply]
    rw [show -(-j + 1) = j - 1 by ring, hD (j - 1) (by omega), mul_zero]
  have hDs : Above (Dsym p : K[T;T⁻¹]) ((N : ℤ) - 1) := by
    exact Above_mono (Above_add hD hiD) (by omega)
  have hiDs : Above (invert (Dsym p : K[T;T⁻¹])) ((N : ℤ) - 1) := by
    rw [Dsym, map_add, involutive_invert]
    exact Above_mono (Above_add hiD hD) (by omega)
  refine ⟨Above_mono (Above_mul (Above_mul hY hiD) (Above_D hD)) (by omega), ?_,
    Above_mono (Above_mul (Above_mul hY hDs) (Above_D hiD)) (by omega), ?_⟩
  · rw [map_mul, map_mul, involutive_invert]
    exact Above_mono (Above_mul (Above_mul hiY hD) hiDP) (by omega)
  · rw [map_mul, map_mul]
    exact Above_mono (Above_mul (Above_mul hiY hiDs) hiDiP) (by omega)

/-- Both original G and X phases vanish from the full mixed sources, before any quadratic projection. -/
theorem lowH_original_quadratic_two_phases (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (T (p : ℤ) * ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent)).coeff (-1) = 0 ∧
      (T (-(p : ℤ)) * ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent)).coeff (-1) = 0 ∧
      (T (p : ℤ) * ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent))).coeff (-1) = 0 ∧
      (T (-(p : ℤ)) * ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent))).coeff (-1) = 0 := by
  have he := lowH_quadratic_source_bounds p hp H hH
  have hA := lowH_two_frobenius_phases_zero p _ he.1 he.2.1
  have hB := lowH_two_frobenius_phases_zero p _ he.2.2.1 he.2.2.2
  exact ⟨hA.1, hA.2, hB.1, hB.2⟩

/-- This is the entire original phi/Bp quadratic source, including all Frobenius phases. -/
theorem lowH_original_quadratic_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    (-(LaurentPolynomial.C (2 / 25 : K) * (4 * T (-(p : ℤ)) - 11) * (4 * T (p : ℤ) - 11)) *
        ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent) +
      LaurentPolynomial.C (1 / 100 : K) * (4 * T (-(p : ℤ)) - 11) * (133 * T (p : ℤ) - 12) *
        ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent))).coeff (-1) =
      (137 / 5 : K) * lowHBranchJs p H - 44 * lowHBranchJ0 p H := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h100 : (100 : K) ≠ 0 := by convert mul_ne_zero (pow_ne_zero 2 h2) (pow_ne_zero 2 h5) using 1; norm_num
  have h25 : (25 : K) ≠ 0 := by convert pow_ne_zero 2 h5 using 1; norm_num
  have ha : (T (-(p : ℤ)) * T (p : ℤ) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have hc0 : -(2 / 25 : K) * (16 + 121) = -(274 / 25 : K) := by ring
  have hc1 : (1 / 100 : K) * (532 + 132) = 166 / 25 := by field_simp [h100, h25]; ring
  have hca := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc0
  have hcb := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc1
  simp only [map_mul, map_add, map_neg, map_ofNat] at hca hcb
  have hA : -(LaurentPolynomial.C (2 / 25 : K) * (4 * T (-(p : ℤ)) - 11) * (4 * T (p : ℤ) - 11)) =
      -LaurentPolynomial.C (274 / 25 : K) + LaurentPolynomial.C (88 / 25 : K) * T (-(p : ℤ)) +
        LaurentPolynomial.C (88 / 25 : K) * T (p : ℤ) := by
    have hc : -(2 / 25 : K) * (-44) = 88 / 25 := by ring
    have he := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
    simp only [map_mul, map_neg, map_ofNat] at he
    linear_combination -16 * LaurentPolynomial.C (2 / 25 : K) * ha + hca +
      (T (-(p : ℤ)) + T (p : ℤ)) * he
  have hB : LaurentPolynomial.C (1 / 100 : K) * (4 * T (-(p : ℤ)) - 11) * (133 * T (p : ℤ) - 12) =
      LaurentPolynomial.C (166 / 25 : K) - LaurentPolynomial.C (12 / 25 : K) * T (-(p : ℤ)) -
        LaurentPolynomial.C (1463 / 100 : K) * T (p : ℤ) := by
    have hc : (1 / 100 : K) * 48 = 12 / 25 := by field_simp [h100, h25]; ring
    have he := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
    simp only [map_mul, map_ofNat] at he
    have hc2 : (1 / 100 : K) * 1463 = 1463 / 100 := by ring
    have he2 := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc2
    simp only [map_mul, map_ofNat] at he2
    linear_combination 532 * LaurentPolynomial.C (1 / 100 : K) * ha + hcb -
      T (-(p : ℤ)) * he - T (p : ℤ) * he2
  rw [hA, hB]
  have hz := lowH_original_quadratic_two_phases p hp H hH
  simp only [mul_assoc] at hz
  simp only [add_mul, sub_mul, mul_assoc, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_neg, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.neg_apply,
    neg_mul, C_mul_coeff, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2,
    mul_zero, add_zero, sub_zero]
  have he :
      -LaurentPolynomial.C (274 / 25 : K) *
          ((lowHCubicY H).toLaurent * invert (Dstar p).toLaurent * D (Dstar p).toLaurent) +
        LaurentPolynomial.C (166 / 25 : K) *
          ((lowHCubicY H).toLaurent * Dsym p * D (invert (Dstar p).toLaurent)) =
      LaurentPolynomial.C (166 / 25 : K) *
          ((lowHCubicY H).toLaurent * Dsym p * D (Dsym p)) -
        LaurentPolynomial.C (88 / 5 : K) *
          ((lowHCubicY H).toLaurent * Dsym p * D (Dstar p).toLaurent) +
        LaurentPolynomial.C (274 / 25 : K) *
          ((lowHCubicY H).toLaurent * (Dstar p).toLaurent * D (Dstar p).toLaurent) := by
    have hc : (166 / 25 : K) + 274 / 25 = 88 / 5 := by field_simp [h25, h5]; ring
    have hcc := congrArg (LaurentPolynomial.C : K → K[T;T⁻¹]) hc
    simp only [map_add] at hcc
    simp only [Dsym, map_add]
    linear_combination -((lowHCubicY H).toLaurent *
      ((Dstar p).toLaurent + invert (Dstar p).toLaurent) * D (Dstar p).toLaurent) * hcc
  have hres := congrArg (fun F : K[T;T⁻¹] => F.coeff (-1)) he
  rw [lowH_branch_quadratic_residue p hp H hH h0] at hres
  simpa only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_neg,
    Finsupp.add_apply, Finsupp.neg_apply, neg_mul, C_mul_coeff, mul_assoc] using hres

end WPFieldAssembly.ActualBpairContraction
