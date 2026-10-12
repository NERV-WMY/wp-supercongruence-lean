import WPFiniteJWeightedResidue
import WPFiniteZSupport
import WPActualFinalConsumer

open scoped Polynomial LaurentPolynomial
open Polynomial

namespace WPFieldAssembly.ResidualProjection

variable {K : Type*} [Field K]

/-- The original weighted p-shift is retained for every j. -/
noncomputable def Ij (p j : ℕ) (G : K[X]) : K :=
  (WPFiniteNC122Residue.canceledDensity G).coeff
    ((p - 1) / 2 + j * p + 1)

theorem polar_projection (m : ℕ) (G : K[X]) :
    (LaurentPolynomial.T (m : ℤ) *
      LaurentPolynomial.invert
        (WPFiniteNC122Residue.canceledDensity G).toLaurent).coeff (-1) =
      (WPFiniteNC122Residue.canceledDensity G).coeff (m + 1) := by
  have hs := WPFiniteJCarrier.shifted_coeff
    (1 : K) (m : ℤ) (-1)
    (LaurentPolynomial.invert
      (WPFiniteNC122Residue.canceledDensity G).toLaurent)
  simp only [map_one, one_mul] at hs
  rw [hs, LaurentPolynomial.invert_apply,
    show -((-1 : ℤ) - (m : ℤ)) = ((m + 1 : ℕ) : ℤ) by omega,
    WPFiniteJCarrier.toLaurent_coeff_nat]

theorem regular_projection_zero (m : ℕ) (R : K[X]) :
    (LaurentPolynomial.T (m : ℤ) * R.toLaurent).coeff (-1) = 0 := by
  have hs := WPFiniteJCarrier.shifted_coeff
    (1 : K) (m : ℤ) (-1) R.toLaurent
  simp only [map_one, one_mul] at hs
  rw [hs]
  exact WPFiniteJCarrier.toLaurent_coeff_outside R _
    (Or.inl (by omega))

theorem projection_with_regular_part (m : ℕ) (G R : K[X]) :
    (LaurentPolynomial.T (m : ℤ) *
      (LaurentPolynomial.invert
          (WPFiniteNC122Residue.canceledDensity G).toLaurent +
        R.toLaurent)).coeff (-1) =
      (WPFiniteNC122Residue.canceledDensity G).coeff (m + 1) := by
  rw [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    polar_projection, regular_projection_zero, add_zero]

theorem canceledDensity_sub_constant (G : K[X]) :
    WPFiniteNC122Residue.canceledDensity (G - C (G.coeff 0)) =
      WPFiniteNC122Residue.canceledDensity G := by
  have hd : (G - C (G.coeff 0)).divX = G.divX := by
    ext n
    simp [coeff_divX]
  unfold WPFiniteNC122Residue.canceledDensity
  rw [hd]

theorem Ij_sub_constant (p j : ℕ) (G : K[X]) :
    Ij p j (G - C (G.coeff 0)) = Ij p j G := by
  unfold Ij
  rw [canceledDensity_sub_constant]

theorem Ij_add (p j : ℕ) (G H : K[X]) :
    Ij p j (G + H) = Ij p j G + Ij p j H := by
  simp [Ij, WPFiniteNC122Residue.canceledDensity,
    divX_add, add_comp, add_mul, coeff_add]

theorem Ij_C_mul (p j : ℕ) (a : K) (G : K[X]) :
    Ij p j (C a * G) = a * Ij p j G := by
  simp [Ij, WPFiniteNC122Residue.canceledDensity,
    divX_C_mul, mul_comp, C_comp, mul_assoc]

theorem Ij_C (p j : ℕ) (a : K) : Ij p j (C a) = 0 := by
  simp [Ij, WPFiniteNC122Residue.canceledDensity]

theorem original_density_without_constant
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (G : K[X]) (x : K) (hx : x ≠ 0)
    (hx4 : x - 4 ≠ 0) (h4x1 : 4 * x - 1 ≠ 0) :
    (WPFiniteNC122Residue.canceledDensity G).eval x⁻¹ =
      (G.eval ((4 - x) ^ 2 * (4 * x - 1) / (125 * x ^ 3)) -
        G.coeff 0) *
      ((WPFiniteNC122Residue.VP : K[X]).derivative.eval x /
        WPFiniteNC122Residue.VP.eval x) := by
  have hz : (G - C (G.coeff 0)).eval 0 = 0 := by
    simp [coeff_zero_eq_eval_zero]
  have he := WPFiniteNC122Residue.original_density_eval
    p hp (G - C (G.coeff 0)) hz x hx hx4 h4x1
  rw [canceledDensity_sub_constant] at he
  simpa only [eval_sub, eval_C] using he

theorem VP_origin_value :
    (WPFiniteNC122Residue.VP : K[X]).eval 0 = 4 / 125 := by
  simp [WPFiniteNC122Residue.VP, div_eq_mul_inv, mul_comm]

theorem VP_origin_ne_zero
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteNC122Residue.VP : K[X]).eval 0 ≠ 0 := by
  have h4 : (4 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 4
      (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 :=
    WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega))
  have h125 : (125 : K) ≠ 0 := by
    rw [show (125 : K) = 5 ^ 3 by ring]
    exact pow_ne_zero _ h5
  rw [VP_origin_value]
  exact div_ne_zero h4 h125

theorem canceledDensity_degree_le
    (G : K[X]) (D : ℕ) (hD : 0 < D) (hG : G.natDegree ≤ D) :
    (WPFiniteNC122Residue.canceledDensity G).natDegree ≤ 3 * D := by
  have hd : G.divX.natDegree ≤ D - 1 := by
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hQ : (WPFiniteNC122Residue.Qrev : K[X]).natDegree ≤ 3 := by
    unfold WPFiniteNC122Residue.Qrev
    compute_degree
  have hF : (WPFiniteNC122Residue.Frev : K[X]).natDegree ≤ 3 := by
    unfold WPFiniteNC122Residue.Frev
    compute_degree
  unfold WPFiniteNC122Residue.canceledDensity
  exact Polynomial.natDegree_mul_le.trans
    ((Nat.add_le_add
      (Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul hd hQ)) hF).trans
        (by omega))

/-- This bound applies to low corrections, not to the whole U squared norm. -/
theorem low_correction_both_projections_zero
    (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
    (G : K[X]) (hG : G.natDegree ≤ p / 6) (j : ℕ) :
    Ij p j G = 0 := by
  unfold Ij
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hd := canceledDensity_degree_le G (p / 6) (by omega) hG
  have h6 := Nat.div_mul_le_self p 6
  have hhalf := WPFiniteWSource.half_exponent p hp
  omega

end WPFieldAssembly.ResidualProjection
