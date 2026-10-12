import WPFieldAssembly.ActualBpairLowHLogBands
import WPFieldAssembly.ActualBpairLowHIntegralRelations
import WPFieldAssembly.ActualBpairLowHWeightedIntegral
import WPFieldAssembly.ActualBpairLowHRegularSources

open scoped Polynomial LaurentPolynomial
open Polynomial WPFiniteProductTail WPFiniteLaurentDifferential
open LaurentPolynomial (T)
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: This is the entire remaining log source IR71h, after
the literal affine sources, for all p >= 19 and degree H <= floor(p/6).
Both proper ends, the full cutoff p-1, all phases and the original simple
origin subtraction are retained. The two auxiliary integrals are cancelled
together; no endpoint value, actual-u identification or kernel is assumed. -/

/-- The complete original four-term log density, including its simple origin pole. -/
noncomputable def lowHRemainingLogDensity (p : ℕ) (RD JQ Q : K[X]) (y0 : K) : K[T;T⁻¹] :=
  LaurentPolynomial.C (4 / 75 : K) * (4 * T (-(p : ℤ)) - 11) *
      (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
        (lowHLog p (1 / 4)).toLaurent) * RD.toLaurent -
    LaurentPolynomial.C (1 / 180 : K) * (15 + 8 * T (-(p : ℤ))) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
      (JQ.toLaurent - LaurentPolynomial.C (3 * y0) * T (-1)) -
    LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ)) *
      ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent -
    LaurentPolynomial.C (2 / 15 : K) * (4 * T (-(p : ℤ)) - 11) *
      (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
        (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent

/-- Whole-source coefficient extraction uses both endpoints and the literal origin indices. -/
theorem lowH_remaining_log_full_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (RD JQ Q : K[X]) (hRD : RD.natDegree < p - 1)
    (hJQ : JQ.natDegree < p - 1) (hQ : Q.natDegree < p - 1) (y0 : K) :
    (lowHRemainingLogDensity p RD JQ Q y0).coeff (-1) =
      -(16 / 75 : K) * ((lowHIntegralP p RD).eval 4 - (lowHIntegralP p RD).eval (1 / 4)) +
      (2 / 45 : K) * ((1 / 4) * (lowHIntegralP p JQ).eval 4 -
        4 * (lowHIntegralP p JQ).eval (1 / 4)) +
      (2 / 3 : K) * ((1 / 4) * (lowHIntegralP p Q).eval 4 -
        4 * (lowHIntegralP p Q).eval (1 / 4)) +
      (8 / 15 : K) * ((lowHIntegralP p Q).eval 4 - (lowHIntegralP p Q).eval (1 / 4)) := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := by convert pow_ne_zero 2 h2 using 1; norm_num
  have h15 : (15 : K) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h45 : (45 : K) ≠ 0 := by convert mul_ne_zero h3 h15 using 1; norm_num
  have h75 : (75 : K) ≠ 0 := by convert mul_ne_zero h5 h15 using 1; norm_num
  have h180 : (180 : K) ≠ 0 := by convert mul_ne_zero h4 h45 using 1; norm_num
  have hrd := lowHLogBands_phi_pair p hp RD hRD
  have hqq := lowHLogBands_phi_pair p hp Q hQ
  have hj := lowHLogBands_difference_density p hp JQ hJQ (15 : K) 8 (3 * y0)
  have hq := lowHLogBands_difference_density p hp Q hQ (0 : K) 1 0
  simp only [map_ofNat] at hj
  simp only [map_zero, map_one, zero_add, one_mul, zero_mul, sub_zero] at hq
  unfold lowHRemainingLogDensity
  rw [show LaurentPolynomial.C (4 / 75 : K) * (4 * T (-(p : ℤ)) - 11) *
        (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
          (lowHLog p (1 / 4)).toLaurent) * RD.toLaurent =
      LaurentPolynomial.C (4 / 75 : K) * ((4 * T (-(p : ℤ)) - 11) *
        (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
          (lowHLog p (1 / 4)).toLaurent) * RD.toLaurent) by ring,
    show LaurentPolynomial.C (1 / 180 : K) * (15 + 8 * T (-(p : ℤ))) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (JQ.toLaurent - LaurentPolynomial.C (3 * y0) * T (-1)) =
      LaurentPolynomial.C (1 / 180 : K) * ((15 + 8 * T (-(p : ℤ))) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) *
        (JQ.toLaurent - LaurentPolynomial.C (3 * y0) * T (-1))) by ring,
    show LaurentPolynomial.C (2 / 3 : K) * T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent =
      LaurentPolynomial.C (2 / 3 : K) * (T (-(p : ℤ)) *
        ((lowHLog p 4).toLaurent - (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent) by ring,
    show LaurentPolynomial.C (2 / 15 : K) * (4 * T (-(p : ℤ)) - 11) *
        (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
          (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent =
      LaurentPolynomial.C (2 / 15 : K) * ((4 * T (-(p : ℤ)) - 11) *
        (4 * (lowHLog p 4).toLaurent - LaurentPolynomial.C (1 / 4 : K) *
          (lowHLog p (1 / 4)).toLaurent) * Q.toLaurent) by ring]
  simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, C_mul_coeff, hrd, hqq, hj, hq]
  field_simp [h2, h3, h4, h5, h15, h45, h75, h180]
  ring

theorem lowHIntegralP_C_mul (p : ℕ) (a : K) (R : K[X]) :
    lowHIntegralP p (C a * R) = C a * lowHIntegralP p R := by
  have hz : lowHIntegralP p (0 : K[X]) = 0 := by
    simp only [lowHIntegralP, mul_zero, unitPrimitiveP, coeff_zero, zero_mul,
      Finset.sum_const_zero, map_zero]
  have he := lowHIntegralP_add_C_mul p a 0 R
  simpa only [zero_add, hz] using he

/-- The original D derivative is multiplied by y before both proper ends are cancelled. -/
theorem lowH_remaining_log_D_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHCubicY H * (Dstar p).derivative =
      C (5 / 2 : K) * (lowHBranchYQuotient H - lowHWeightedBranchDensity ((p - 1) / 2) H) := by
  have he := Dstar_cleared_source (K := K) p hp
  rw [lowHBranchYQuotient_source H h0]
  have hw : lowHWeightedBranchDensity ((p - 1) / 2) H =
      lowHBranchYQuotient H * WPFiniteWSource.squaredCoordinate ^ ((p - 1) / 2) := by
    simp only [lowHWeightedBranchDensity, lowHBranchYQuotient, lowHLinearS,
      WPFiniteWSource.squaredCoordinate, one_div]
  rw [hw]
  linear_combination lowHBranchYQuotient H * he

theorem lowH_remaining_log_JQ_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHJQDensity H).natDegree < p - 1 := by
  have hdiv : H.divX.natDegree ≤ p / 6 - 1 := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hcomp : (H.divX.comp (WPFiniteNC122Residue.VP : K[X])).natDegree ≤ (p / 6 - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hdiv lowHCubicV_degree)
  have ha : ((X : K[X]) - C (1 / 4 : K)).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hb : ((X : K[X]) - C (4 : K)).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
  have hscalar : (-C (16 / 125 : K)).natDegree ≤ 0 := by simp
  have hleftA : (-C (16 / 125 : K) * (X - C (4 : K))).natDegree ≤ 1 := by
    calc
      _ ≤ (-C (16 / 125 : K)).natDegree + (X - C (4 : K)).natDegree :=
        natDegree_mul_le
      _ ≤ 0 + 1 := Nat.add_le_add hscalar hb
  have hfactorA : (-C (16 / 125 : K) * (X - C (4 : K)) *
      (X - C (1 / 4 : K))).natDegree ≤ 2 := by
    calc
      _ ≤ (-C (16 / 125 : K) * (X - C (4 : K))).natDegree +
          (X - C (1 / 4 : K)).natDegree := natDegree_mul_le
      _ ≤ 1 + 1 := Nat.add_le_add hleftA ha
  have hpower : (((X : K[X]) - C (1 / 4 : K)) ^ 2).natDegree ≤ 2 := by
    calc
      _ ≤ 2 * ((X : K[X]) - C (1 / 4 : K)).natDegree := natDegree_pow_le
      _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 ha
  have hfactorB : (-C (16 / 125 : K) * ((X : K[X]) - C (1 / 4 : K)) ^ 2).natDegree ≤ 2 := by
    calc
      _ ≤ (-C (16 / 125 : K)).natDegree +
          (((X : K[X]) - C (1 / 4 : K)) ^ 2).natDegree := natDegree_mul_le
      _ ≤ 0 + 2 := Nat.add_le_add hscalar hpower
  have hA : (lowHBranchAQuotient H).natDegree ≤ 2 + (p / 6 - 1) * 3 := by
    unfold lowHBranchAQuotient
    exact natDegree_mul_le.trans (Nat.add_le_add hfactorA hcomp)
  have hB : (lowHBranchBQuotient H).natDegree ≤ 2 + (p / 6 - 1) * 3 := by
    unfold lowHBranchBQuotient
    exact natDegree_mul_le.trans (Nat.add_le_add hfactorB hcomp)
  have hY := lowHCubicY_degree (p / 6) H hH
  have hYdiv : (lowHCubicY H).divX.natDegree ≤ 3 * (p / 6) - 1 := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hband := lowH_prime_six_band p hp
  unfold lowHJQDensity
  exact (natDegree_sub_le _ _).trans_lt (max_lt
    ((natDegree_add_le _ _).trans_lt (max_lt (by omega)
      ((natDegree_C_mul_le _ _).trans_lt (by omega))))
    ((natDegree_C_mul_le _ _).trans_lt (by omega)))

private theorem lowH_remaining_regular_density (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) :
    lowHBranchYQuotient H = lowHRegularBranchDensity H := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have hc4 := congrArg (Polynomial.C : K →+* K[X]) (mul_one_div_cancel h4)
  have hc15 := congrArg (Polynomial.C : K →+* K[X]) (mul_one_div_cancel h15)
  simp only [one_div, map_mul, map_ofNat, map_one] at hc4 hc15
  unfold lowHBranchYQuotient lowHRegularBranchDensity lowHBranchAQuotient lowHBranchBQuotient
  simp only [div_eq_mul_inv, map_mul, map_ofNat, one_mul]
  linear_combination
    -(Polynomial.C ((125 : K)⁻¹) * H.divX.comp WPFiniteNC122Residue.VP * (4 * X - 1)) * hc15 -
    (Polynomial.C ((125 : K)⁻¹) * H.divX.comp WPFiniteNC122Residue.VP * Polynomial.C ((15 : K)⁻¹) *
      (-4 * X + 4 * Polynomial.C ((4 : K)⁻¹) - 15)) * hc4

/-- The two unweighted pieces cancel before the full weighted endpoint difference is evaluated. -/
theorem lowH_remaining_log_unweighted_contraction (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    -(16 / 75 : K) *
        ((lowHIntegralP p (lowHCubicY H * (Dstar p).derivative)).eval 4 -
          (lowHIntegralP p (lowHCubicY H * (Dstar p).derivative)).eval (1 / 4)) +
      (8 / 15 : K) * ((lowHIntegralP p (lowHBranchYQuotient H)).eval 4 -
        (lowHIntegralP p (lowHBranchYQuotient H)).eval (1 / 4)) =
      (8 / 75 : K) * (lowHEulerJ p H).eval 1 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := by convert mul_ne_zero h3 h5 using 1; norm_num
  have h75 : (75 : K) ≠ 0 := by convert mul_ne_zero h5 h15 using 1; norm_num
  have hI : lowHIntegralP p (lowHCubicY H * (Dstar p).derivative) =
      C (5 / 2 : K) * (lowHIntegralP p (lowHBranchYQuotient H) -
        lowHIntegralP p (lowHWeightedBranchDensity ((p - 1) / 2) H)) := by
    rw [lowH_remaining_log_D_density p hp H h0, lowHIntegralP_C_mul]
    congr 1
    simpa only [map_one, one_mul] using
      lowHIntegralP_sub_C_mul p (1 : K) (lowHBranchYQuotient H)
        (lowHWeightedBranchDensity ((p - 1) / 2) H)
  rw [hI, eval_mul, eval_mul, eval_C, eval_C, eval_sub, eval_sub]
  calc
    _ = (8 / 15 : K) *
        ((lowHIntegralP p (lowHWeightedBranchDensity ((p - 1) / 2) H)).eval 4 -
          (lowHIntegralP p (lowHWeightedBranchDensity ((p - 1) / 2) H)).eval (1 / 4)) := by
      field_simp [h2, h3, h5, h15, h75]
      ring
    _ = _ := by
      rw [lowHWeightedBranchDensity_prime_ends p hp H hH]
      field_simp [h3, h5, h15, h75]
      ring

/-- The whole remaining log group retains both auxiliary integrals until their common cancellation. -/
theorem lowH_original_remaining_log_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (h0 : H.coeff 0 = 0) :
    (lowHRemainingLogDensity p (lowHCubicY H * (Dstar p).derivative)
      (lowHJQDensity H) (lowHBranchYQuotient H) ((lowHCubicY H).coeff 0)).coeff (-1) =
      (8 / 75 : K) * (lowHEulerJ p H).eval 1 +
      (1 / 6 : K) * (lowHqPrimitive p H).eval (WPFiniteNC122Residue.VP.eval 0) -
      (2 / 15 : K) * ((1 / 4) * originPrimitive p (lowHCubicY H) 4 -
        4 * originPrimitive p (lowHCubicY H) (1 / 4)) := by
  have hb := lowH_prime_six_band p hp
  have hm := lowH_auxiliary_middle_contraction p hp (p / 6) (by omega) hb.2 H hH h0
  rw [← lowH_remaining_regular_density p hp H] at hm
  have hu := lowH_remaining_log_unweighted_contraction p hp H hH h0
  rw [lowH_remaining_log_full_residue p hp _ _ _
    (lowH_regular_D_density_degree p hp H hH)
    (lowH_remaining_log_JQ_degree p hp H hH)
    (lowH_regular_branch_density_degree p hp H hH)]
  linear_combination hu + hm

end WPFieldAssembly.ActualBpairContraction
