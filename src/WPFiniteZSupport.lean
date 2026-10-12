import WPFiniteZSource

open scoped Polynomial LaurentPolynomial

namespace WPFiniteZSupport

open LaurentPolynomial WPFiniteLaurentDifferential WPFiniteZSource
  WPFiniteABSourceTail WPFiniteWSource WPFinitePSource WPFiniteLVSource
  WPFiniteLVSharp WPFiniteJCarrier WPFiniteJSource

variable {K : Type*} [Field K]

theorem coordinate_degree : (squaredCoordinate : K[X]).natDegree ≤ 1 := by
  unfold squaredCoordinate
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((Polynomial.natDegree_add_le _ _).trans (by simp))

theorem pole_degree : (Abar : K[X]).natDegree ≤ 2 := by
  have hleft : (4 - Polynomial.X : K[X]).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hright : (4 * Polynomial.X - 1 : K[X]).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le _ (by simp)
    change (Polynomial.C (4 : K) * Polynomial.X).natDegree ≤ 1
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add hleft hright).trans (by norm_num))

theorem R_bound (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Above (R p : K[T;T⁻¹]) ((p : ℤ) + ((p - 1) / 2 : ℕ) - 2) := by
  have hA := Above_pow (Above_toLaurent (Abar : K[X]) 2 pole_degree) (p - 1)
  have hS := Above_pow (Above_toLaurent (squaredCoordinate : K[X]) 1 coordinate_degree) ((p - 1) / 2)
  have he := Above_C_mul (Above_mul (Above_shift hA (-(p : ℤ))) hS) (1 / 2 : K)
  have hid : (R p : K[T;T⁻¹]) = C (1 / 2 : K) *
      (T (-(p : ℤ)) * Abar.toLaurent ^ (p - 1) * squaredCoordinate.toLaurent ^ ((p - 1) / 2)) := by
    unfold R
    ring
  rw [hid]
  exact Above_mono he (by omega)

theorem A_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    (A p (W p) u : K[X]).natDegree ≤ (p - 1) / 2 - 1 := by
  unfold A
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp)
    ((Polynomial.natDegree_C_mul_le _ _).trans (W_degree p hp)))

theorem P_bound (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    Above (P p u : K[T;T⁻¹]) ((p : ℤ) + ((p - 1) / 2 : ℕ) - 1) := by
  have hA := A_degree (K := K) p hp u
  have hB := Above_toLaurent (B0 p (W p) u) (p - 1) (original_phase_degrees p hp u).1
  have hC := Above_toLaurent (Cminus p u) (p - 1) (original_phase_degrees p hp u).2
  unfold P
  exact Above_mono (Above_add (Above_add
    (Above_shift (Above_toLaurent _ _ hA) (p : ℤ)) hB)
      (Above_shift hC (-(p : ℤ)))) (by omega)

theorem phase_bound (p : ℕ) : Above (phase p : K[T;T⁻¹]) (p : ℤ) := by
  have hpos : Above (T (p : ℤ) : K[T;T⁻¹]) (p : ℤ) := by
    simpa only [map_one, one_mul] using Above_monomial (1 : K) (p : ℤ)
  have hneg : Above (T (-(p : ℤ)) : K[T;T⁻¹]) (-(p : ℤ)) := by
    simpa only [map_one, one_mul] using Above_monomial (1 : K) (-(p : ℤ))
  change Above (C (17 : K) - C (4 : K) * T (p : ℤ) - C (4 : K) * T (-(p : ℤ))) _
  exact Above_mono (Above_sub (Above_sub (Above_C (17 : K))
    (Above_C_mul hpos 4)) (Above_C_mul hneg 4)) (by omega)

theorem GJ_bound (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Above (GJ p : K[T;T⁻¹]) (3 * (p : ℤ) - 3) := by
  have hH := Above_toLaurent (HJP p : K[X]) (2 * p - 3) (HJP_natDegree_le p hp)
  have hHi := Above_invert_toLaurent (HJP p : K[X])
  rw [GJ_phase]
  have he := Above_C_mul (Above_mul (phase_bound (K := K) p) (Above_add hH hHi)) (1 / 45 : K)
  rw [mul_assoc]
  exact Above_mono he (by omega)

theorem bracket_bound (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Above (-P p u + C (1 / 3 : K) * ((LV p).toLaurent -
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent))
        (((p - 1) / 2 : ℕ) - 1 : ℤ) := by
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3 (Finset.mem_Ico.mpr (by omega))
  have hc : (C (1 / 3 : K) * 3 : K[T;T⁻¹]) = 1 := by
    change C (1 / 3 : K) * C (3 : K) = 1
    rw [← map_mul, one_div_mul_cancel h3, map_one]
  have hid : (-P p u + C (1 / 3 : K) * ((LV p).toLaurent -
      T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent)) =
      C (1 / 3 : K) * ((positiveDifference p u).toLaurent -
        3 * T (-(p : ℤ)) * (Cminus p u).toLaurent -
          T (-(((p - 1) / 2 : ℕ) : ℤ)) * invert (LV p).toLaurent) := by
    linear_combination C (1 / 3 : K) * remainder_phases (K := K) p u + P p u * hc
  have hpos := Above_toLaurent (positiveDifference p u) ((p - 1) / 2 - 1)
    (positiveDifference_sharp_bound p hp u hu)
  have hC := Above_toLaurent (Cminus p u) (p - 1) (original_phase_degrees p hp u).2
  have href := Above_shift (Above_invert_toLaurent (LV p : K[X])) (-(((p - 1) / 2 : ℕ) : ℤ))
  have hnegative := Above_C_mul (Above_shift hC (-(p : ℤ))) (3 : K)
  rw [hid]
  have he := Above_C_mul (Above_sub (Above_sub hpos hnegative) href) (1 / 3 : K)
  have hrew : (3 * T (-(p : ℤ)) * (Cminus p u).toLaurent : K[T;T⁻¹]) =
      C (3 : K) * (T (-(p : ℤ)) * (Cminus p u).toLaurent) := by
    simp only [map_ofNat]
    ring
  rw [hrew]
  exact Above_mono he (by omega)

theorem Z_initial_bound (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) (u : K) :
    Above (Z p u : K[T;T⁻¹]) (3 * (p : ℤ) - 3) := by
  have he := half_exponent p hp
  have hsq := Above_C_mul (Above_pow (P_bound (K := K) p hp u) 2) (1 / 2 : K)
  rw [Z, neg_mul]
  exact Above_mono (Above_add (Above_neg hsq) (GJ_bound p hp)) (by omega)

theorem Z_derivative_bound (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Above (D (Z p u : K[T;T⁻¹])) (2 * (p : ℤ) - 4) := by
  have he := half_exponent p hp
  have hfirst := Above_mul (R_bound (K := K) p hp) (bracket_bound p hp u hu)
  have hsecond := Above_C_mul (Above_shift (P_bound (K := K) p hp u) (-1)) (1 / 2 : K)
  rw [Z_derivative p hp u]
  have hrew : (C (1 / 2 : K) * T (-1) * P p u) = C (1 / 2 : K) * (T (-1) * P p u) := by ring
  rw [hrew]
  exact Above_mono (Above_add hfirst hsecond) (by omega)

/-- Entire finite NC116 high support; no native quotient comparison is assumed. -/
theorem actual_finite_whole_support (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (u : K) (hu : u ^ 2 = 1 / 5) :
    Above (Z p u : K[T;T⁻¹]) (2 * (p : ℤ)) ∧
      (Z p u : K[T;T⁻¹]).coeff (2 * (p : ℤ) - 2) = 0 ∧
      (Z p u : K[T;T⁻¹]).coeff (2 * (p : ℤ) - 1) = 0 :=
  whole_high_band p hp (Z p u) (Z_initial_bound p hp u) (Z_derivative_bound p hp u hu)

/-- The entire square coefficient remains; no derivative-invisible value is assigned. -/
theorem actual_finite_2p_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Z p u : K[T;T⁻¹]).coeff (2 * (p : ℤ)) =
      -(1 / 2 : K) * (P p u ^ 2).coeff (2 * (p : ℤ)) -
        4 * (HJP p : K[X]).coeff p / 45 := by
  have hc := shifted_coeff (1 / 2 : K) 0 (2 * (p : ℤ)) (P p u ^ 2)
  simp only [T_zero, mul_one, sub_zero] at hc
  rw [Z, neg_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, hc, actual_GJ_2p_coefficient p hp]
  ring

/-- All five square phases are read; the shifted upper indices 3p and 4p vanish by degree. -/
theorem P_square_2p_coefficient (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (P p u ^ 2 : K[T;T⁻¹]).coeff (2 * (p : ℤ)) =
      (A p (W p) u : K[X]).coeff 0 ^ 2 + 2 * (A p (W p) u * B0 p (W p) u).coeff p := by
  have hA := A_degree (K := K) p hp u
  have hB := (original_phase_degrees (K := K) p hp u).1
  have hC := (original_phase_degrees (K := K) p hp u).2
  have hBB : ((B0 p (W p) u : K[X]) ^ 2).natDegree ≤ 2 * p - 2 :=
    (Polynomial.natDegree_pow_le_of_le 2 hB).trans (by omega)
  have hCC : ((Cminus p u : K[X]) ^ 2).natDegree ≤ 2 * p - 2 :=
    (Polynomial.natDegree_pow_le_of_le 2 hC).trans (by omega)
  have hBC : ((B0 p (W p) u : K[X]) * Cminus p u).natDegree ≤ 2 * p - 2 :=
    Polynomial.natDegree_mul_le.trans ((Nat.add_le_add hB hC).trans (by omega))
  have hAC : ((A p (W p) u : K[X]) * Cminus p u).natDegree ≤ 2 * p - 2 :=
    Polynomial.natDegree_mul_le.trans ((Nat.add_le_add hA hC).trans (by omega))
  have hrow : ((B0 p (W p) u : K[X]) ^ 2 + 2 * A p (W p) u * Cminus p u).natDegree ≤ 2 * p - 2 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le hBB
    rw [mul_assoc]
    change (Polynomial.C (2 : K) * (A p (W p) u * Cminus p u)).natDegree ≤ _
    exact (Polynomial.natDegree_C_mul_le _ _).trans hAC
  have hrow0 : (((B0 p (W p) u : K[X]) ^ 2 + 2 * A p (W p) u * Cminus p u).toLaurent).coeff
      (2 * (p : ℤ)) = 0 := toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hBC0 : ((B0 p (W p) u * Cminus p u : K[X]).toLaurent).coeff (3 * (p : ℤ)) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hCC0 : (((Cminus p u : K[X]) ^ 2).toLaurent).coeff (4 * (p : ℤ)) = 0 :=
    toLaurent_coeff_outside _ _ (Or.inr (by omega))
  have hA0 : (((A p (W p) u : K[X]) ^ 2).toLaurent).coeff 0 = (A p (W p) u).coeff 0 ^ 2 := by
    calc
      _ = ((A p (W p) u : K[X]) ^ 2).coeff 0 := by
        simpa only [Nat.cast_zero] using toLaurent_coeff_nat ((A p (W p) u : K[X]) ^ 2) 0
      _ = _ := by simp [pow_two, Polynomial.coeff_mul]
  have ht : (T (p : ℤ) * T (-(p : ℤ)) : K[T;T⁻¹]) = 1 := by
    rw [← T_add, add_neg_cancel, T_zero]
  have ht2 : (T (p : ℤ) * T (p : ℤ) : K[T;T⁻¹]) = T (2 * (p : ℤ)) := by
    rw [← T_add]; congr 1; ring
  have htm2 : (T (-(p : ℤ)) * T (-(p : ℤ)) : K[T;T⁻¹]) = T (-(2 * (p : ℤ))) := by
    rw [← T_add]; congr 1; ring
  have hexpand : (P p u ^ 2 : K[T;T⁻¹]) =
      C (1 : K) * T (2 * (p : ℤ)) * ((A p (W p) u) ^ 2).toLaurent +
      C (2 : K) * T (p : ℤ) * (A p (W p) u * B0 p (W p) u).toLaurent +
      ((B0 p (W p) u) ^ 2 + 2 * A p (W p) u * Cminus p u).toLaurent +
      C (2 : K) * T (-(p : ℤ)) * (B0 p (W p) u * Cminus p u).toLaurent +
      C (1 : K) * T (-(2 * (p : ℤ))) * ((Cminus p u) ^ 2).toLaurent := by
    simp only [P, map_add, map_mul, map_pow, map_ofNat, map_one, one_mul]
    linear_combination (A p (W p) u).toLaurent ^ 2 * ht2 +
      (Cminus p u).toLaurent ^ 2 * htm2 +
      2 * (A p (W p) u).toLaurent * (Cminus p u).toLaurent * ht
  rw [hexpand]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, shifted_coeff, one_mul]
  rw [show 2 * (p : ℤ) - 2 * p = 0 by ring, show 2 * (p : ℤ) - p = p by ring,
    show 2 * (p : ℤ) - -p = 3 * p by ring,
    show 2 * (p : ℤ) - -(2 * p) = 4 * p by ring, hA0, hrow0, hBC0, hCC0, toLaurent_coeff_nat]
  ring

/-- The original derivative-invisible phase, with no value or zero hypothesis. -/
theorem actual_finite_original_2p (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (u : K) :
    (Z p u : K[T;T⁻¹]).coeff (2 * (p : ℤ)) =
      -(A p (W p) u : K[X]).coeff 0 ^ 2 / 2 -
        (A p (W p) u * B0 p (W p) u).coeff p - 4 * (HJP p : K[X]).coeff p / 45 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2 (Finset.mem_Ico.mpr (by omega))
  have hc : (1 / 2 : K) * 2 = 1 := one_div_mul_cancel h2
  rw [actual_finite_2p_coefficient p hp u, P_square_2p_coefficient p hp u]
  linear_combination -(A p (W p) u * B0 p (W p) u).coeff p * hc

end WPFiniteZSupport
