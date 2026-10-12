import WPFieldAssembly.ActualBpairLowHEndpoints
import WPFieldAssembly.ActualBpairBranchSquare
import WPFieldAssembly.GreenLaurentOperators

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/-- The literal polynomial y/Abar, after cancelling both original proper ends. -/
noncomputable def lowHBranchYQuotient (H : K[X]) : K[X] :=
  Polynomial.C (1 / 125 : K) * (4 * X - 1) * H.divX.comp WPFiniteNC122Residue.VP

noncomputable def lowHBranchTailPolynomial (p : ℕ) (H : K[X]) : K[X] :=
  lowHBranchYQuotient H * branchPolynomial p

theorem lowHBranchYQuotient_source (H : K[X]) (h0 : H.coeff 0 = 0) :
    lowHCubicY H = WPFiniteZSource.Abar * lowHBranchYQuotient H := by
  rw [lowHCubicY_source H h0]
  simp only [WPFiniteNC122Residue.VP, WPFiniteZSource.Abar, lowHBranchYQuotient, one_div]
  ring

theorem lowHBranchYQuotient_degree (d : ℕ) (hd : 1 ≤ d) (H : K[X]) (hH : H.natDegree ≤ d) :
    (lowHBranchYQuotient H).natDegree ≤ 3 * d - 2 := by
  have hh : H.divX.natDegree ≤ d - 1 := by rw [natDegree_divX_eq_natDegree_tsub_one]; omega
  have hc : (H.divX.comp (WPFiniteNC122Residue.VP : K[X])).natDegree ≤ (d - 1) * 3 :=
    natDegree_comp_le.trans (Nat.mul_le_mul hh lowHCubicV_degree)
  have hx : (4 * (X : K[X]) - 1).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_C_mul_le _ _).trans (by simp)) (by simp))
  have he : (lowHBranchYQuotient H).natDegree ≤ 1 + (d - 1) * 3 :=
    natDegree_mul_le.trans (Nat.add_le_add ((natDegree_C_mul_le _ _).trans hx) hc)
  omega

/-- The retained delta=N-3d sharpens the full reciprocal bound in both prime classes. -/
theorem lowHBranchTailPolynomial_degree (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHBranchTailPolynomial p H).natDegree ≤
      p - 6 - ((p - 1) / 2 - 3 * (p / 6)) := by
  have hs := lowH_prime_six_band p hp
  have hN : 2 * ((p - 1) / 2) + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> omega
  have hd := lowHBranchYQuotient_degree (p / 6) (by omega) H hH
  have hb := branchPolynomial_degree (K := K) p hp
  have he : (lowHBranchTailPolynomial p H).natDegree ≤
      3 * (p / 6) - 2 + ((p - 1) / 2 - 3) := natDegree_mul_le.trans (Nat.add_le_add hd hb)
  omega

/-- This is the entire actual branch factor, before any residue or phase selection. -/
theorem lowH_Dsym_full_branch_factor (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (Dsym p : K[T;T⁻¹]) =
      T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2 + 1) *
          (branchPolynomial p).toLaurent := by
  calc
    _ = T (-(((p - 1) / 2 - 1 : ℕ) : ℤ)) *
        (T (((p - 1) / 2 - 1 : ℕ) : ℤ) * Dsym p) := by
      rw [← mul_assoc, ← T_add, neg_add_cancel, T_zero, one_mul]
    _ = _ := by
      rw [← branchNumerator_toLaurent p hp, branchPolynomial_factor p hp,
        map_mul, map_pow]
      ring

private theorem lowH_squaredCoordinate_frobenius (p : ℕ) [Fact p.Prime] [CharP K p]
    (_hp : 19 ≤ p) : (WPFiniteWSource.squaredCoordinate : K[X]) ^ p =
      Polynomial.C (1 / 5 : K) * (X ^ p + 1) := by
  have h5 : (5 : K) ^ p = 5 := WPFiniteField.natCast_pow_char p 5
  rw [WPFiniteWSource.squaredCoordinate, mul_pow, ← map_pow, inv_pow, h5,
    add_pow_char, one_pow]
  rw [one_div]

/-- The whole reciprocal branch term is the sum of one regular and one negative phase. -/
theorem lowH_branch_reciprocal_full_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) :
    (lowHBranchYQuotient H).toLaurent * Dsym p *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ)) =
      LaurentPolynomial.C (1 / 5 : K) * (T 2 + T (2 - (p : ℤ))) *
        (lowHBranchTailPolynomial p H).toLaurent := by
  let N := (p - 1) / 2
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  have hs := congrArg (fun Q : K[X] => Q.toLaurent) (lowH_squaredCoordinate_frobenius (K := K) p hp)
  simp only [map_pow, map_mul, map_add, map_one, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, T_pow, mul_one] at hs
  rw [lowH_Dsym_full_branch_factor p hp]
  change (lowHBranchYQuotient H).toLaurent *
      (T (-((N - 1 : ℕ) : ℤ)) * WPFiniteWSource.squaredCoordinate.toLaurent ^ (N + 1) *
        (branchPolynomial p).toLaurent) * WPFiniteWSource.squaredCoordinate.toLaurent ^ N *
      T (-(N : ℤ)) = _
  rw [show (lowHBranchYQuotient H).toLaurent *
      (T (-((N - 1 : ℕ) : ℤ)) * WPFiniteWSource.squaredCoordinate.toLaurent ^ (N + 1) *
        (branchPolynomial p).toLaurent) * WPFiniteWSource.squaredCoordinate.toLaurent ^ N *
      T (-(N : ℤ)) =
      T (-((N - 1 : ℕ) : ℤ)) * T (-(N : ℤ)) *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ (N + 1 + N) *
        (lowHBranchTailPolynomial p H).toLaurent by
      rw [lowHBranchTailPolynomial, map_mul, pow_add]
      ring]
  rw [show N + 1 + N = p by omega, hs]
  rw [show T (-((N - 1 : ℕ) : ℤ)) * T (-(N : ℤ)) = T (2 - (p : ℤ)) by
    rw [← T_add]
    congr 1
    omega]
  rw [show T (2 - (p : ℤ)) *
      (LaurentPolynomial.C (1 / 5 : K) * (T (p : ℤ) + 1)) =
      LaurentPolynomial.C (1 / 5 : K) * (T 2 + T (2 - (p : ℤ))) by
    calc
      _ = LaurentPolynomial.C (1 / 5 : K) *
          (T (2 - (p : ℤ)) * T (p : ℤ) + T (2 - (p : ℤ))) := by ring
      _ = _ := by rw [← T_add, show 2 - (p : ℤ) + p = 2 by omega]]

/-- Both full phases vanish by the actual branch factor and sharp support bound. -/
theorem lowH_branch_reciprocal_residue_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    ((lowHBranchYQuotient H).toLaurent * Dsym p *
        WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
        T (-(((p - 1) / 2 : ℕ) : ℤ))).coeff (-1) = 0 := by
  have hd := lowHBranchTailPolynomial_degree p hp H hH
  rw [lowH_branch_reciprocal_full_source p hp H, mul_assoc, C_mul_coeff, add_mul,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  have hpos := WPFiniteJCarrier.shifted_coeff (1 : K) 2 (-1)
    (lowHBranchTailPolynomial p H).toLaurent
  have hneg := WPFiniteJCarrier.shifted_coeff (1 : K) (2 - (p : ℤ)) (-1)
    (lowHBranchTailPolynomial p H).toLaurent
  simp only [map_one, one_mul] at hpos hneg
  rw [hpos, hneg, show (-1 : ℤ) - 2 = -3 by omega,
    WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)),
    show (-1 : ℤ) - (2 - (p : ℤ)) = ((p - 3 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat,
    coeff_eq_zero_of_natDegree_lt (by omega), add_zero, mul_zero]

end WPFieldAssembly.ActualBpairContraction
