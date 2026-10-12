import WPFieldAssembly.ActualBpairLowHBranchQuadratic
import WPFieldAssembly.ActualBpairLowHIntegralRelations

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential WPFiniteNC122Residue
open WPFieldAssembly.GreenLaurentOperators

namespace WPFieldAssembly.ActualBpairContraction

variable {K : Type*} [Field K]

set_option maxHeartbeats 1800000

/- STATEMENT_FIDELITY: For every prime p >= 19, arbitrary characteristic-p
   field K, and H of degree at most floor(p/6), the original IR71k D-linear
   and q-log sources use y=H(V), the literal Q=y/Abar polynomial source, Dstar
   and its actual reciprocal. The cleared source attachment assumes H(0)=0.
   Both Frobenius phases and the complete y/x origin pole are retained, and
   the degree bounds exclude both shifted residues before their coefficients
   at zero are selected. The -3*y0*D0/10 term remains. There is no generated
   finite manifest or assertion of the final W_p identity. -/

noncomputable def lowHLinearYOverX (H : K[X]) : K[T;T⁻¹] :=
  T (-1) * (lowHCubicY H).toLaurent

noncomputable def lowHLinearYQLog (H : K[X]) : K[T;T⁻¹] :=
  ((18 - 12 * X) * lowHBranchYQuotient H).toLaurent -
    LaurentPolynomial.C (3 : K) * lowHLinearYOverX H

/-- The literal derivative of V identifies the existing y*l polynomial. -/
theorem lowH_linear_ylog_polynomial (H : K[X]) :
    lowHqCubicDensity H = (33 - 12 * X) * lowHBranchYQuotient H := by
  unfold lowHqCubicDensity lowHBranchYQuotient
  simp only [VP, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_sub, derivative_ofNat, derivative_X, zero_sub, derivative_pow,
    Nat.cast_ofNat, C_ofNat, Nat.reduceSub, pow_one, derivative_one, sub_zero]
  simp only [one_div]
  ring

/-- Both logarithmic densities are attached to the original cleared y/Abar source. -/
theorem lowH_linear_cleared_sources (H : K[X]) (h0 : H.coeff 0 = 0) :
    (WPFiniteZSource.Abar : K[X]).toLaurent * (lowHqCubicDensity H).toLaurent =
        (33 - 12 * T 1) * (lowHCubicY H).toLaurent ∧
      (WPFiniteZSource.Abar : K[X]).toLaurent *
          (lowHLinearYQLog H + LaurentPolynomial.C (3 : K) * lowHLinearYOverX H) =
        (18 - 12 * T 1) * (lowHCubicY H).toLaurent := by
  rw [lowH_linear_ylog_polynomial, lowHBranchYQuotient_source H h0]
  simp only [lowHLinearYQLog, map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
  constructor <;> ring

theorem lowH_linear_density_relation (H : K[X]) :
    lowHLinearYQLog H - (lowHqCubicDensity H).toLaurent +
        LaurentPolynomial.C (3 : K) * lowHLinearYOverX H =
      -LaurentPolynomial.C (15 : K) * (lowHBranchYQuotient H).toLaurent := by
  rw [lowH_linear_ylog_polynomial]
  simp only [lowHLinearYQLog, map_mul, map_sub, map_ofNat, Polynomial.toLaurent_X]
  ring

/-- The actual y/Abar quotient is the existing regular proper-end density. -/
theorem lowH_linear_regular_density (p : ℕ) [Fact p.Prime] [CharP K p]
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
    -(Polynomial.C ((125 : K)⁻¹) * H.divX.comp VP * (4 * X - 1)) * hc15 -
    (Polynomial.C ((125 : K)⁻¹) * H.divX.comp VP * Polynomial.C ((15 : K)⁻¹) *
      (-4 * X + 4 * Polynomial.C ((4 : K)⁻¹) - 15)) * hc4

/-- The existing polynomial J_Q density retains its original y0/x subtraction. -/
theorem lowH_linear_JQ_origin_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) :
    lowHLinearYQLog H = (lowHJQDensity H).toLaurent -
      LaurentPolynomial.C (3 * (lowHCubicY H).coeff 0) * T (-1) := by
  have hpoly : lowHJQDensity H =
      (18 - 12 * X) * lowHBranchYQuotient H - 3 * (lowHCubicY H).divX := by
    have he := lowH_auxiliary_density_identity p hp H
    rw [← lowH_linear_regular_density p hp H, lowH_linear_ylog_polynomial] at he
    linear_combination he
  have hy := congrArg (fun P : K[X] => P.toLaurent) (X_mul_divX_add (lowHCubicY H))
  simp only [map_add, map_mul, Polynomial.toLaurent_X, Polynomial.toLaurent_C] at hy
  have hx : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by
    rw [← T_add]
    norm_num
  have hz : lowHLinearYOverX H = (lowHCubicY H).divX.toLaurent +
      LaurentPolynomial.C ((lowHCubicY H).coeff 0) * T (-1) := by
    rw [lowHLinearYOverX, ← hy, mul_add, ← mul_assoc, hx, one_mul]
    ring
  rw [lowHLinearYQLog, hpoly, hz]
  simp only [map_sub, map_mul, map_ofNat]
  ring

private theorem linear_two_phases_zero (p : ℕ) (F : K[T;T⁻¹])
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

private theorem linear_density_bounds (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (a b c : K) :
    Above (((Polynomial.C a + Polynomial.C b * X) * lowHBranchYQuotient H).toLaurent +
        LaurentPolynomial.C c * lowHLinearYOverX H) ((((p - 1) / 2 : ℕ) : ℤ) - 1) ∧
      Above (invert (((Polynomial.C a + Polynomial.C b * X) * lowHBranchYQuotient H).toLaurent +
        LaurentPolynomial.C c * lowHLinearYOverX H)) 1 := by
  let N := (p - 1) / 2
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  have hb := lowH_prime_six_band p hp
  have hQ : (lowHBranchYQuotient H).natDegree ≤ N - 2 := by
    have he := lowHBranchYQuotient_degree (p / 6) (by omega) H hH
    omega
  have hA : (Polynomial.C a + Polynomial.C b * X : K[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le (by simp) (by
      exact (natDegree_mul_le (p := Polynomial.C b) (q := X)).trans (by simp)))
  have hAQ : ((Polynomial.C a + Polynomial.C b * X) * lowHBranchYQuotient H).natDegree ≤ N - 1 :=
    ((natDegree_mul_le (p := Polynomial.C a + Polynomial.C b * X)
      (q := lowHBranchYQuotient H)).trans (add_le_add hA hQ)).trans (by omega)
  have hpoly := Above_toLaurent _ (N - 1) hAQ
  have hpoly' : Above (((Polynomial.C a + Polynomial.C b * X) *
      lowHBranchYQuotient H).toLaurent) ((N : ℤ) - 1) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] using hpoly
  have hY : Above (lowHCubicY H).toLaurent (N : ℤ) := by
    apply Above_toLaurent
    have he := lowHCubicY_degree (p / 6) H hH
    omega
  have hz : Above (lowHLinearYOverX H) ((N : ℤ) - 1) := by
    simpa only [lowHLinearYOverX, neg_add_eq_sub] using Above_shift hY (-1)
  have hiz : Above (invert (lowHLinearYOverX H)) 1 := by
    rw [lowHLinearYOverX, map_mul, invert_T]
    simpa only [neg_neg, add_zero] using Above_shift (Above_invert_toLaurent (lowHCubicY H)) 1
  constructor
  · exact Above_mono (Above_add hpoly' (Above_C_mul hz c)) (by omega)
  · have hic : invert (LaurentPolynomial.C c * lowHLinearYOverX H) =
        LaurentPolynomial.C c * invert (lowHLinearYOverX H) := by
      rw [map_mul, invert_C]
    rw [map_add, hic]
    exact Above_mono (Above_add (Above_invert_toLaurent _)
      (Above_C_mul hiz c)) (by omega)

/-- Each actual density and each Dstar/Dvee product has both full phases excluded. -/
theorem lowH_linear_all_phases_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6)
    (A : K[T;T⁻¹])
    (hA : A = (lowHqCubicDensity H).toLaurent ∨ A = lowHLinearYQLog H ∨
      A = lowHLinearYOverX H ∨ A = (lowHBranchYQuotient H).toLaurent) :
    ((T (p : ℤ) * A).coeff (-1) = 0 ∧ (T (-(p : ℤ)) * A).coeff (-1) = 0) ∧
      ((T (p : ℤ) * ((Dstar p).toLaurent * A)).coeff (-1) = 0 ∧
        (T (-(p : ℤ)) * ((Dstar p).toLaurent * A)).coeff (-1) = 0) ∧
      ((T (p : ℤ) * (invert (Dstar p).toLaurent * A)).coeff (-1) = 0 ∧
        (T (-(p : ℤ)) * (invert (Dstar p).toLaurent * A)).coeff (-1) = 0) := by
  let N := (p - 1) / 2
  have hN : 2 * N + 1 = p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with he | ho <;> dsimp [N] <;> omega
  have hb : Above A ((N : ℤ) - 1) ∧ Above (invert A) 1 := by
    rcases hA with rfl | rfl | rfl | rfl
    · have he := linear_density_bounds p hp H hH (33 : K) (-12) 0
      simpa only [lowH_linear_ylog_polynomial, map_ofNat, map_neg, neg_mul,
        sub_eq_add_neg, map_zero, zero_mul, add_zero] using he
    · have he := linear_density_bounds p hp H hH (18 : K) (-12) (-3)
      simpa only [lowHLinearYQLog, map_ofNat, map_neg, neg_mul,
        sub_eq_add_neg] using he
    · have he := linear_density_bounds p hp H hH 0 0 1
      simpa only [map_zero, zero_mul, zero_add, map_one, one_mul] using he
    · have he := linear_density_bounds p hp H hH 1 0 0
      simpa only [map_zero, zero_mul, zero_add, add_zero, map_one, one_mul] using he
  have hD : Above (Dstar p : K[X]).toLaurent ((N : ℤ) - 1) := by
    have he := Above_toLaurent (Dstar p : K[X]) (N - 1) (Dstar_degree p hp)
    simpa only [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one] using he
  have hiD := Above_invert_toLaurent (Dstar p : K[X])
  refine ⟨linear_two_phases_zero p A (Above_mono hb.1 (by omega))
      (Above_mono hb.2 (by omega)), ?_, ?_⟩
  · apply linear_two_phases_zero
    · exact Above_mono (Above_mul hD hb.1) (by omega)
    · rw [map_mul]
      exact Above_mono (Above_mul hiD hb.2) (by omega)
  · apply linear_two_phases_zero
    · exact Above_mono (Above_mul hiD hb.1) (by omega)
    · rw [map_mul, involutive_invert]
      exact Above_mono (Above_mul hD hb.2) (by omega)

private theorem linear_polynomial_residue (P : K[X]) : P.toLaurent.coeff (-1) = 0 :=
  WPFiniteJCarrier.toLaurent_coeff_outside P (-1) (Or.inl (by omega))

private theorem linear_y_over_x_residue (H : K[X]) :
    (lowHLinearYOverX H).coeff (-1) = (lowHCubicY H).coeff 0 := by
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1) (lowHCubicY H).toLaurent
  simp only [map_one, one_mul, sub_self] at he
  have hzero := WPFiniteJCarrier.toLaurent_coeff_nat (lowHCubicY H) 0
  simp only [Nat.cast_zero] at hzero
  rw [hzero] at he
  exact he

private theorem linear_D_y_over_x_residue (p : ℕ) (H : K[X]) :
    ((Dstar p).toLaurent * lowHLinearYOverX H).coeff (-1) =
      (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 := by
  rw [show (Dstar p).toLaurent * lowHLinearYOverX H =
      T (-1) * ((lowHCubicY H) * Dstar p).toLaurent by
        simp only [lowHLinearYOverX, map_mul]; ring]
  have he := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (-1)
    ((lowHCubicY H) * Dstar p).toLaurent
  simp only [map_one, one_mul, sub_self] at he
  have hzero := WPFiniteJCarrier.toLaurent_coeff_nat ((lowHCubicY H) * Dstar p) 0
  simp only [Nat.cast_zero] at hzero
  rw [hzero] at he
  simpa only [Polynomial.mul_coeff_zero] using he

theorem lowH_linear_origin_density_residues (p : ℕ) (H : K[X]) :
    (lowHLinearYQLog H).coeff (-1) = -3 * (lowHCubicY H).coeff 0 ∧
      ((Dstar p).toLaurent * lowHLinearYQLog H).coeff (-1) =
        -3 * (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 := by
  constructor
  · rw [lowHLinearYQLog, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      linear_polynomial_residue, C_mul_coeff, linear_y_over_x_residue]
    ring
  · rw [lowHLinearYQLog, mul_sub,
      show (Dstar p).toLaurent * (LaurentPolynomial.C (3 : K) * lowHLinearYOverX H) =
        LaurentPolynomial.C (3 : K) * ((Dstar p).toLaurent * lowHLinearYOverX H) by ring,
      ← map_mul, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      linear_polynomial_residue, C_mul_coeff, linear_D_y_over_x_residue]
    ring

noncomputable def lowHOriginalDLinearSource (p : ℕ) (H : K[X]) : K[T;T⁻¹] :=
  let G := T (p : ℤ)
  let Xp := T (-(p : ℤ))
  let Ds := (Dstar p : K[X]).toLaurent
  let Dv := invert Ds
  let yl := (lowHqCubicDensity H).toLaurent
  let ylq := lowHLinearYQLog H
  let z := lowHLinearYOverX H
  let Q := (lowHBranchYQuotient H).toLaurent
  (LaurentPolynomial.C (5 / 6 : K) - LaurentPolynomial.C (11 / 8 : K) * G) * Ds * ylq +
    (LaurentPolynomial.C (11 / 15 : K) - LaurentPolynomial.C (4 / 15 : K) * Xp) * Dv * ylq +
    LaurentPolynomial.C (1 / 15 : K) * (4 * Xp - 11) * (Ds + Dv) * yl -
    LaurentPolynomial.C (1 / 5 : K) * (4 * Xp - 11) * (Ds + Dv) * z +
    LaurentPolynomial.C (1 / 40 : K) * (4 * Xp - 11) * (133 * G - 12) * Ds * Q +
    LaurentPolynomial.C (1 / 8 : K) * (4 * Xp - 11) * (33 * G - 28) * Dv * Q

private theorem linear_source_decompose (p : ℕ) (H : K[X]) :
    lowHOriginalDLinearSource p H =
      LaurentPolynomial.C (5 / 6 : K) * ((Dstar p).toLaurent * lowHLinearYQLog H) +
      LaurentPolynomial.C (11 / 15 : K) * (invert (Dstar p).toLaurent * lowHLinearYQLog H) -
      LaurentPolynomial.C (1 / 15 : K) *
        (11 * ((Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent) +
          11 * (invert (Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent)) +
      LaurentPolynomial.C (1 / 5 : K) *
        (11 * ((Dstar p).toLaurent * lowHLinearYOverX H) +
          11 * (invert (Dstar p).toLaurent * lowHLinearYOverX H)) +
      LaurentPolynomial.C (1 / 40 : K) *
        (664 * ((Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent)) +
      LaurentPolynomial.C (1 / 8 : K) *
        (440 * (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent)) -
      LaurentPolynomial.C (11 / 8 : K) *
        (T (p : ℤ) * ((Dstar p).toLaurent * lowHLinearYQLog H)) -
      LaurentPolynomial.C (4 / 15 : K) *
        (T (-(p : ℤ)) * (invert (Dstar p).toLaurent * lowHLinearYQLog H)) +
      LaurentPolynomial.C (1 / 15 : K) *
        (4 * (T (-(p : ℤ)) * ((Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent)) +
          4 * (T (-(p : ℤ)) * (invert (Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent))) -
      LaurentPolynomial.C (1 / 5 : K) *
        (4 * (T (-(p : ℤ)) * ((Dstar p).toLaurent * lowHLinearYOverX H)) +
          4 * (T (-(p : ℤ)) * (invert (Dstar p).toLaurent * lowHLinearYOverX H))) -
      LaurentPolynomial.C (1 / 40 : K) *
        (48 * (T (-(p : ℤ)) * ((Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent)) +
          1463 * (T (p : ℤ) * ((Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent))) -
      LaurentPolynomial.C (1 / 8 : K) *
        (112 * (T (-(p : ℤ)) * (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent)) +
          363 * (T (p : ℤ) * (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent))) := by
  have hGX : (T (p : ℤ) : K[T;T⁻¹]) * T (-(p : ℤ)) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  unfold lowHOriginalDLinearSource
  dsimp only
  linear_combination
    (532 * LaurentPolynomial.C (1 / 40 : K) * (Dstar p).toLaurent *
        (lowHBranchYQuotient H).toLaurent +
      132 * LaurentPolynomial.C (1 / 8 : K) * invert (Dstar p).toLaurent *
        (lowHBranchYQuotient H).toLaurent) * hGX

/-- The full original D-linear source retains its y0*D0 origin contribution and 44*J0. -/
theorem lowH_original_D_linear_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) :
    (lowHOriginalDLinearSource p H).coeff (-1) =
      -(3 / 10 : K) * (lowHCubicY H).coeff 0 * (Dstar p : K[X]).coeff 0 +
        44 * lowHBranchJ0 p H := by
  have hyl := lowH_linear_all_phases_zero p hp H hH
    (lowHqCubicDensity H).toLaurent (Or.inl rfl)
  have hylq := lowH_linear_all_phases_zero p hp H hH
    (lowHLinearYQLog H) (Or.inr (Or.inl rfl))
  have hz := lowH_linear_all_phases_zero p hp H hH
    (lowHLinearYOverX H) (Or.inr (Or.inr (Or.inl rfl)))
  have hQ := lowH_linear_all_phases_zero p hp H hH
    (lowHBranchYQuotient H).toLaurent (Or.inr (Or.inr (Or.inr rfl)))
  have hDyl : ((Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent).coeff (-1) = 0 := by
    rw [← map_mul]
    exact linear_polynomial_residue _
  have hDQ : ((Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent).coeff (-1) = 0 := by
    rw [← map_mul]
    exact linear_polynomial_residue _
  have hJ : lowHBranchJ0 p H =
      (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent).coeff (-1) := by
    rw [lowHBranchJ0, Dsym, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [show (lowHBranchYQuotient H).toLaurent * (Dstar p).toLaurent =
      (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent by ring, hDQ, zero_add,
      mul_comm (lowHBranchYQuotient H).toLaurent]
  have hrel :
      (invert (Dstar p).toLaurent * lowHLinearYQLog H).coeff (-1) =
        (invert (Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent).coeff (-1) -
          3 * (invert (Dstar p).toLaurent * lowHLinearYOverX H).coeff (-1) -
          15 * (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent).coeff (-1) := by
    have hs : invert (Dstar p).toLaurent * lowHLinearYQLog H -
          invert (Dstar p).toLaurent * (lowHqCubicDensity H).toLaurent +
          LaurentPolynomial.C (3 : K) * (invert (Dstar p).toLaurent * lowHLinearYOverX H) =
        -LaurentPolynomial.C (15 : K) *
          (invert (Dstar p).toLaurent * (lowHBranchYQuotient H).toLaurent) := by
      linear_combination invert (Dstar p).toLaurent * lowH_linear_density_relation H
    have he := congrArg (fun F : K[T;T⁻¹] => F.coeff (-1)) hs
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, Finsupp.add_apply,
      Finsupp.sub_apply, neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, C_mul_coeff] at he
    linear_combination he
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h8 : (8 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 8
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  rw [linear_source_decompose]
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply,
    show (11 : K[T;T⁻¹]) = LaurentPolynomial.C (11 : K) by rw [map_ofNat],
    show (4 : K[T;T⁻¹]) = LaurentPolynomial.C (4 : K) by rw [map_ofNat],
    show (664 : K[T;T⁻¹]) = LaurentPolynomial.C (664 : K) by rw [map_ofNat],
    show (440 : K[T;T⁻¹]) = LaurentPolynomial.C (440 : K) by rw [map_ofNat],
    show (48 : K[T;T⁻¹]) = LaurentPolynomial.C (48 : K) by rw [map_ofNat],
    show (1463 : K[T;T⁻¹]) = LaurentPolynomial.C (1463 : K) by rw [map_ofNat],
    show (112 : K[T;T⁻¹]) = LaurentPolynomial.C (112 : K) by rw [map_ofNat],
    show (363 : K[T;T⁻¹]) = LaurentPolynomial.C (363 : K) by rw [map_ofNat],
    C_mul_coeff, hDyl, hDQ, hylq.2.1.1, hylq.2.2.2, hyl.2.1.2, hyl.2.2.2,
    hz.2.1.2, hz.2.2.2, hQ.2.1.1, hQ.2.1.2, hQ.2.2.1, hQ.2.2.2,
    mul_zero, zero_add, add_zero, sub_zero,
    (lowH_linear_origin_density_residues p H).2, linear_D_y_over_x_residue]
  rw [hrel, hJ]
  field_simp [h5, h6, h8, h10, h15]
  ring

noncomputable def lowHOriginalQLogConstantSource (p : ℕ) (H : K[X]) (κ q2 : K) : K[T;T⁻¹] :=
  -LaurentPolynomial.C (1 / 72 : K) * (15 * T (p : ℤ) + 8) *
    (LaurentPolynomial.C κ - LaurentPolynomial.C (4 * q2 / 5) * T (-(p : ℤ))) *
    lowHLinearYQLog H

/-- The full q-log source keeps both phases until the actual density bounds exclude them. -/
theorem lowH_original_qlog_constant_residue (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (H : K[X]) (hH : H.natDegree ≤ p / 6) (κ q2 : K) :
    (lowHOriginalQLogConstantSource p H κ q2).coeff (-1) =
      (κ / 3 - q2 / 2) * (lowHCubicY H).coeff 0 := by
  have hphase := (lowH_linear_all_phases_zero p hp H hH
    (lowHLinearYQLog H) (Or.inr (Or.inl rfl))).1
  have hGX : (T (p : ℤ) : K[T;T⁻¹]) * T (-(p : ℤ)) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have hsource : lowHOriginalQLogConstantSource p H κ q2 =
      -LaurentPolynomial.C (1 / 72 : K) *
        (LaurentPolynomial.C κ * (15 * (T (p : ℤ) * lowHLinearYQLog H)) +
          LaurentPolynomial.C κ * (8 * lowHLinearYQLog H) -
          LaurentPolynomial.C (4 * q2 / 5) * (15 * lowHLinearYQLog H) -
          LaurentPolynomial.C (4 * q2 / 5) * (8 * (T (-(p : ℤ)) * lowHLinearYQLog H))) := by
    unfold lowHOriginalQLogConstantSource
    linear_combination
      (15 * LaurentPolynomial.C (1 / 72 : K) * LaurentPolynomial.C (4 * q2 / 5) *
        lowHLinearYQLog H) * hGX
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h72 : (72 : K) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 h2) (pow_ne_zero 2 h3) using 1
    ring
  rw [hsource]
  simp only [neg_mul, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply,
    C_mul_coeff, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply,
    show (15 : K[T;T⁻¹]) = LaurentPolynomial.C (15 : K) by rw [map_ofNat],
    show (8 : K[T;T⁻¹]) = LaurentPolynomial.C (8 : K) by rw [map_ofNat],
    hphase.1, hphase.2, (lowH_linear_origin_density_residues p H).1,
    mul_zero, sub_zero, zero_add]
  field_simp [h2, h3, h5, h72]
  ring

end WPFieldAssembly.ActualBpairContraction
