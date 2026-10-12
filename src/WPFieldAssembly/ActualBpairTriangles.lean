import WPFieldAssembly.ActualBpairMixedTail
import WPFieldAssembly.ActualBpairBranchSquare
import WPFinitePrimitiveTransport

open scoped BigOperators Polynomial LaurentPolynomial
open Polynomial WPFiniteKSource WPFiniteAffineLog WPFiniteProductTail
open LaurentPolynomial (T invert invert_apply invert_C involutive_invert)

namespace WPFieldAssembly.ActualBpairContraction

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

/-- Moving a whole phase changes only the strict threshold, on every Laurent exponent. -/
theorem fullStrictPositive_phase_shift (p k r : ℕ) (hr : r ≤ k) (F : K[T;T⁻¹]) :
    fullStrictPositive p k (T ((r * p : ℕ) : ℤ) * F) =
      fullStrictPositive p (k - r) F := by
  ext j
  rw [fullStrictPositive_coeff, fullStrictPositive_coeff]
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]
  · rw [if_neg hj, if_neg hj]
    have hs := WPFiniteJCarrier.shifted_coeff (1 : K) ((r * p : ℕ) : ℤ)
      ((k * p + j : ℕ) : ℤ) F
    simp only [map_one, one_mul] at hs
    rw [hs]
    congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hr]
    ring

/-- A positive upper phase retains the complete polynomial, including its old origin. -/
theorem fullStrictPositive_upper_polynomial (p : ℕ) (hp : 0 < p) (P : K[X]) :
    fullStrictPositive p 0 (T (p : ℤ) * P.toLaurent) = X ^ p * P := by
  ext j
  rw [fullStrictPositive_coeff, zero_mul, zero_add, coeff_X_pow_mul']
  by_cases hj : j = 0
  · subst j
    rw [if_pos rfl, if_neg (by omega : ¬ p ≤ 0)]
  · rw [if_neg hj]
    have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (p : ℤ) (j : ℤ) P.toLaurent
    simp only [map_one, one_mul] at hs
    rw [hs]
    by_cases hjp : p ≤ j
    · rw [if_pos hjp, show (j : ℤ) - p = ((j - p : ℕ) : ℤ) by omega,
        WPFiniteJCarrier.toLaurent_coeff_nat]
    · rw [if_neg hjp]
      exact WPFiniteJCarrier.toLaurent_coeff_outside P _ (Or.inl (by omega))

private theorem unitPrimitiveP_remove_origin (p : ℕ) (W : K[X]) (z : K) :
    unitPrimitiveP p (W - C (W.coeff 0)) z = unitPrimitiveP p W z := by
  unfold unitPrimitiveP
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_sub, coeff_C, if_neg (by have := (Finset.mem_Ico.mp hi).1; omega), sub_zero]

/-- The same polynomial primitive realizes H(z,w) with its actual zero at w=0. -/
noncomputable def branchHPolynomial (p : ℕ) (z : K) : K[X] :=
  unitPrimitiveP p (-C (3 : K) * Dstar p) z

theorem branchHPolynomial_eval (p : ℕ) (z w : K) :
    (branchHPolynomial p z).eval w = branchH p z w := by
  rw [branchHPolynomial, unitPrimitiveP_eval]
  rfl

theorem branchHPolynomial_zero (p : ℕ) (z : K) :
    (branchHPolynomial p z).eval 0 = 0 := unitPrimitiveP_zero p _ z

theorem branchHPolynomial_source (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (X - C z) * (branchHPolynomial p z).derivative =
      -C (3 : K) * Dstar p - C ((-C (3 : K) * Dstar p : K[X]).eval z) := by
  let W : K[X] := -C (3 : K) * Dstar p
  have hW : W.natDegree < p := by
    dsimp only [W]
    rw [← C_neg]
    exact (natDegree_C_mul_le _ _).trans_lt ((Dstar_degree p hp).trans_lt (by omega))
  have hW0 : (W - C (W.coeff 0)).natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hW (by
      have hp0 := (Fact.out : p.Prime).pos
      simpa using hp0))
  have h := unitPrimitiveP_source p (W - C (W.coeff 0)) hW0 (by simp) z
  rw [unitPrimitiveP_remove_origin, eval_sub, eval_C, map_sub] at h
  change (X - C z) * (unitPrimitiveP p W z).derivative = W - C (W.eval z)
  linear_combination h

theorem branchHPolynomial_degree (p : ℕ) (z : K) :
    (branchHPolynomial p z : K[X]).natDegree ≤ p - 1 := unitPrimitiveP_degree p _ z

/-- A proved source, degree band and zero origin identify the same literal H polynomial. -/
theorem branchHPolynomial_unique (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) (Q : K[X]) (hQ : Q.natDegree < p) (hQ0 : Q.eval 0 = 0)
    (hsource : (X - C z) * Q.derivative =
      -C (3 : K) * Dstar p - C ((-C (3 : K) * Dstar p : K[X]).eval z)) :
    Q = branchHPolynomial p z := by
  let W : K[X] := -C (3 : K) * Dstar p
  have hW : W.natDegree < p := by
    dsimp only [W]
    rw [← C_neg]
    exact (natDegree_C_mul_le _ _).trans_lt ((Dstar_degree p hp).trans_lt (by omega))
  have hW0 : (W - C (W.coeff 0)).natDegree < p :=
    (natDegree_sub_le _ _).trans_lt (max_lt hW (by
      have hp0 := (Fact.out : p.Prime).pos
      simpa using hp0))
  have he : (X - C z) * Q.derivative =
      W - C (W.coeff 0) - C ((W - C (W.coeff 0)).eval z) := by
    rw [eval_sub, eval_C, map_sub]
    linear_combination hsource
  have h := WPFinitePrimitiveTransport.unitPrimitiveP_unique p (W - C (W.coeff 0))
    hW0 (by simp) z Q hQ hQ0 he
  rw [unitPrimitiveP_remove_origin] at h
  exact h

/-- The complete ordered triangle includes its k=i diagonal. -/
noncomputable def orderedPrimitivePolynomial (p : ℕ) (W : K[X]) (y : K) : K[X] :=
  ∑ i ∈ Finset.Ico 1 p, ∑ k ∈ Finset.Ico 1 (i + 1),
    C (W.coeff i * y ^ k / (k : K)) * X ^ (i - k)

theorem orderedPrimitivePolynomial_eval (p : ℕ) (W : K[X]) (z y : K) :
    (orderedPrimitivePolynomial p W y).eval z = unitPrimitive p W z y := by
  simp only [orderedPrimitivePolynomial, unitPrimitive, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [div_eq_mul_inv]
  ring

private theorem scaledLog_integer_coeff (p : ℕ) (c : K) (m : ℤ) :
    (((LP p : K[X]).comp (C c * X)).toLaurent).coeff m =
      if 1 ≤ m ∧ m < p then c ^ m.toNat / (m.toNat : K) else 0 := by
  by_cases hm : 0 ≤ m
  · have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    rw [← he, WPFiniteJCarrier.toLaurent_coeff_nat, LP_scaled_coeff]
    congr 1
    exact propext (by omega)
  · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)),
      if_neg (by omega : ¬(1 ≤ m ∧ m < p))]

private theorem ordered_monomial_projection (p i : ℕ) (hi : i ∈ Finset.Ico 1 p)
    (a c : K) :
    LaurentPolynomial.trunc ((C a * X ^ i).toLaurent *
      invert (((LP p : K[X]).comp (C c * X)).toLaurent)) =
      ∑ k ∈ Finset.Ico 1 (i + 1), C (a * c ^ k / (k : K)) * X ^ (i - k) := by
  classical
  have hi' := Finset.mem_Ico.mp hi
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff]
  simp only [map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
    WPFiniteJCarrier.shifted_coeff, invert_apply]
  rw [show -((j : ℤ) - i) = (i : ℤ) - j by omega, scaledLog_integer_coeff,
    finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hj : j < i
  · have hk : i - j ∈ Finset.Ico 1 (i + 1) := Finset.mem_Ico.mpr (by omega)
    rw [if_pos (by omega : 1 ≤ (i : ℤ) - j ∧ (i : ℤ) - j < p),
      show ((i : ℤ) - j).toNat = i - j by omega]
    rw [Finset.sum_eq_single (i - j)]
    · rw [if_pos (by omega : j = i - (i - j))]
      simp only [div_eq_mul_inv]
      ring
    · intro k hk' hne
      have hk'' := Finset.mem_Ico.mp hk'
      rw [if_neg (by omega : j ≠ i - k)]
    · intro hnot
      exact (hnot hk).elim
  · rw [if_neg (by omega : ¬(1 ≤ (i : ℤ) - j ∧ (i : ℤ) - j < p)), mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    rw [if_neg (by omega : j ≠ i - k)]

private theorem scaledLog_zero_coeff (p : ℕ) (c : K) :
    ((LP p : K[X]).comp (C c * X)).coeff 0 = 0 := by
  rw [LP_scaled_coeff, if_neg (by omega)]

private theorem polynomial_full_origin_split (p : ℕ) (W : K[X]) (hW : W.natDegree < p) :
    W = C (W.coeff 0) + ∑ i ∈ Finset.Ico 1 p, C (W.coeff i) * X ^ i := by
  classical
  ext j
  simp only [coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hj : j = 0
  · subst j
    rw [if_pos rfl, if_neg (by simp only [Finset.mem_Ico]; omega), add_zero]
  · rw [if_neg hj, zero_add]
    by_cases hjp : j ∈ Finset.Ico 1 p
    · rw [if_pos hjp]
    · rw [if_neg hjp]
      exact coeff_eq_zero_of_natDegree_lt (hW.trans_le (by
        have hm : ¬(1 ≤ j ∧ j < p) := by simpa only [Finset.mem_Ico] using hjp
        omega))

/-- The nonpositive reciprocal triangle is fixed by the literal finite convolution. -/
theorem log_reciprocal_triangle (p : ℕ) (W : K[X]) (hW : W.natDegree < p) (c : K) :
    LaurentPolynomial.trunc (W.toLaurent * invert
      (((LP p : K[X]).comp (C c * X)).toLaurent)) = orderedPrimitivePolynomial p W c := by
  classical
  have he := polynomial_full_origin_split p W hW
  conv_lhs => rw [he]
  simp only [map_add, map_sum, add_mul, Finset.sum_mul]
  have hz : LaurentPolynomial.trunc (LaurentPolynomial.C (W.coeff 0) *
      invert (((LP p : K[X]).comp (C c * X)).toLaurent)) = 0 := by
    rw [WPFiniteJWeightedResidue.trunc_C_mul, WPFiniteJWeightedResidue.trunc_invert,
      scaledLog_zero_coeff, map_zero, mul_zero]
  rw [Polynomial.toLaurent_C, hz, zero_add]
  unfold orderedPrimitivePolynomial
  apply Finset.sum_congr rfl
  intro i hi
  exact ordered_monomial_projection p i hi (W.coeff i) c

theorem log_reciprocal_triangle_value (p : ℕ) (W : K[X]) (hW : W.natDegree < p)
    (c z : K) :
    (LaurentPolynomial.trunc (W.toLaurent * invert
      (((LP p : K[X]).comp (C c * X)).toLaurent))).eval z = unitPrimitive p W z c := by
  rw [log_reciprocal_triangle p W hW c, orderedPrimitivePolynomial_eval]

/-- The entire nonpositive part is reflected only after the actual product is formed. -/
noncomputable def nonpositiveMixedTriangle (p : ℕ) : K[X] :=
  LaurentPolynomial.trunc (invert ((finiteMixedLog p).toLaurent * invert (Dstar p).toLaurent))

theorem nonpositiveMixedTriangle_value (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) (z : K) :
    (nonpositiveMixedTriangle p : K[X]).eval z =
      (2 / 15 : K) * ((1 / 4 : K) * branchH p z 4 - 4 * branchH p z (1 / 4)) := by
  have hD : (Dstar p : K[X]).natDegree < p := (Dstar_degree p hp).trans_lt (by omega)
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  have he : invert ((finiteMixedLog p).toLaurent * invert (Dstar p).toLaurent) =
      LaurentPolynomial.C (2 / 5 : K) *
        (LaurentPolynomial.C (-(1 / 4 : K)) * ((Dstar p).toLaurent *
          invert (((LP p : K[X]).comp (C (4 : K) * X)).toLaurent)) +
        LaurentPolynomial.C (4 : K) * ((Dstar p).toLaurent *
          invert (((LP p : K[X]).comp (C (1 / 4 : K) * X)).toLaurent))) := by
    simp only [finiteMixedLog, map_mul, map_add, map_neg, Polynomial.toLaurent_C,
      invert_C]
    rw [involutive_invert]
    rw [← map_neg LaurentPolynomial.C]
    ring
  rw [nonpositiveMixedTriangle, he, WPFiniteJWeightedResidue.trunc_C_mul,
    map_add, WPFiniteJWeightedResidue.trunc_C_mul, WPFiniteJWeightedResidue.trunc_C_mul]
  simp only [eval_mul, eval_C, eval_add]
  rw [log_reciprocal_triangle_value p _ hD 4 z,
    log_reciprocal_triangle_value p _ hD (1 / 4) z]
  simp only [branchH_is_Dstar_primitive]
  field_simp [h3, h4, h5, h15]
  ring

/-- Both endpoint weights apply to the complete nonpositive triangle, including its origin. -/
theorem nonpositiveMixedTriangle_weighted (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    2 * (nonpositiveMixedTriangle p : K[X]).eval (1 / 4) +
      (nonpositiveMixedTriangle p : K[X]).eval 4 =
      (2 / 15 : K) * ((1 / 4 : K) * (2 * branchH p (1 / 4) 4 + branchH p 4 4) -
        4 * (2 * branchH p (1 / 4) (1 / 4) + branchH p 4 (1 / 4))) := by
  rw [nonpositiveMixedTriangle_value p hp, nonpositiveMixedTriangle_value p hp]
  ring

noncomputable def nonpositiveDstarTriangle (p : ℕ) : K[X] :=
  LaurentPolynomial.trunc (invert ((Dstar p).toLaurent * invert (Dstar p).toLaurent))

theorem nonpositiveDstarTriangle_polynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) : (nonpositiveDstarTriangle p : K[X]) =
      C (1 / 2 : K) * (branchSquare p - Dstar p ^ 2 - C ((Dstar p : K[X]).coeff 0 ^ 2)) := by
  have he : invert ((Dstar p : K[X]).toLaurent * invert (Dstar p).toLaurent) =
      (Dstar p).toLaurent * invert (Dstar p).toLaurent := by
    rw [map_mul, involutive_invert]
    ring
  rw [nonpositiveDstarTriangle, he]
  have h := Dstar_reciprocal_product_positive (K := K) p hp
  rw [Dstar_reciprocal_product_origin p hp, C_neg] at h
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hc : C (2 : K) * C (1 / 2 : K) = (1 : K[X]) := by
    rw [← map_mul, mul_one_div_cancel h2, map_one]
  apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr h2)
  simp only [C_ofNat] at h hc ⊢
  linear_combination (2 : K[X]) * h +
    (2 * C ((Dstar p : K[X]).coeff 0 ^ 2)) * hc

theorem nonpositiveDstarTriangle_weighted (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    2 * (nonpositiveDstarTriangle p : K[X]).eval (1 / 4) +
      (nonpositiveDstarTriangle p : K[X]).eval 4 =
      (3 / 5 : K) * ((Dstar p : K[X]).eval (1 / 4) + (Dstar p : K[X]).eval 4) ^ 2 -
        (Dstar p : K[X]).eval (1 / 4) ^ 2 - (Dstar p : K[X]).eval 4 ^ 2 / 2 -
          3 * (Dstar p : K[X]).coeff 0 ^ 2 / 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨ha, hb⟩ := branchSquare_endpoints (K := K) p hp
  rw [nonpositiveDstarTriangle_polynomial p hp]
  simp only [eval_mul, eval_C, eval_sub, eval_pow]
  rw [ha, hb]
  field_simp [h2, h5]
  ring

/-- The original Laurent polynomial splits into its strict positive and complete nonpositive parts. -/
theorem whole_projection_decomposition (p : ℕ) (F : K[T;T⁻¹]) :
    F = (fullStrictPositive p 0 F).toLaurent +
      invert (LaurentPolynomial.trunc (invert F)).toLaurent := by
  ext j
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, invert_apply]
  cases j with
  | ofNat n =>
    change F.coeff (n : ℤ) = (fullStrictPositive p 0 F).toLaurent.coeff (n : ℤ) +
      (LaurentPolynomial.trunc (invert F)).toLaurent.coeff (-(n : ℤ))
    rw [WPFiniteJCarrier.toLaurent_coeff_nat, fullStrictPositive_coeff,
      zero_mul, zero_add]
    by_cases hn : n = 0
    · subst n
      rw [if_pos rfl]
      simp only [Nat.cast_zero, neg_zero, zero_add]
      have h0 := WPFiniteJCarrier.toLaurent_coeff_nat (LaurentPolynomial.trunc (invert F)) 0
      simp only [WPFiniteJWeightedResidue.trunc_coeff, invert_apply,
        Nat.cast_zero, neg_zero] at h0
      exact h0.symm
    · rw [if_neg hn, WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)), add_zero]
  | negSucc n =>
    rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)), zero_add,
      show -(Int.negSucc n) = ((n + 1 : ℕ) : ℤ) by omega,
      WPFiniteJCarrier.toLaurent_coeff_nat, WPFiniteJWeightedResidue.trunc_coeff,
      invert_apply]
    congr 1

/-- The two original end weights include the full nonpositive projection, with its origin. -/
theorem fullStrictTail_zero_projection (p : ℕ) (F : K[T;T⁻¹]) (v : Kˣ) (hv : (v : K) = 4) :
    fullStrictTail p 0 F =
      2 * LaurentPolynomial.eval₂ (RingHom.id K) v F +
        LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ F -
      (2 * (LaurentPolynomial.trunc (invert F)).eval (1 / 4) +
        (LaurentPolynomial.trunc (invert F)).eval 4) := by
  have hb := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v)
    (whole_projection_decomposition p F)
  have ha := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹)
    (whole_projection_decomposition p F)
  simp only [map_add, LaurentPolynomial.eval₂_toLaurent, eval₂_id,
    WPFiniteJWeightedResidue.inversion_eval] at hb ha
  simp only [Units.val_inv_eq_inv_val, hv, inv_inv] at hb ha
  rw [fullStrictTail]
  simp only [one_div]
  linear_combination -2 * hb - ha

/-- The full strict cross-product tail retains the exact origin correction. -/
theorem Dstar_reciprocal_product_strict_weighted (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    fullStrictTail p 0 ((Dstar p).toLaurent * invert (Dstar p).toLaurent) =
      (9 / 10 : K) * ((Dstar p : K[X]).eval (1 / 4) + (Dstar p : K[X]).eval 4) ^ 2 -
        (Dstar p : K[X]).eval (1 / 4) ^ 2 / 2 - (Dstar p : K[X]).eval 4 ^ 2 +
          3 * (Dstar p : K[X]).coeff 0 ^ 2 / 2 := by
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  obtain ⟨ha, hb⟩ := branchSquare_endpoints (K := K) p hp
  rw [fullStrictTail, fullStrictPositive]
  simp only [zero_mul, Nat.cast_zero, neg_zero, LaurentPolynomial.T_zero, one_mul]
  rw [Dstar_reciprocal_product_positive p hp]
  simp only [eval_mul, eval_C, eval_add, eval_sub, eval_pow]
  rw [ha, hb]
  field_simp [h2, h5, h10]
  ring

/-- Whole product evaluation removes the complete nonpositive fD triangle exactly once. -/
theorem finiteMixedLog_reciprocalDstar_strict_weighted (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 19 ≤ p) :
    fullStrictTail p 0 ((finiteMixedLog p).toLaurent * invert (Dstar p).toLaurent) =
      2 * (finiteMixedLog p : K[X]).eval 4 * (Dstar p : K[X]).eval (1 / 4) +
        (finiteMixedLog p : K[X]).eval (1 / 4) * (Dstar p : K[X]).eval 4 -
      (2 / 15 : K) * ((1 / 4 : K) * (2 * branchH p (1 / 4) 4 + branchH p 4 4) -
        4 * (2 * branchH p (1 / 4) (1 / 4) + branchH p 4 (1 / 4))) := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K) = 4 := rfl
  rw [fullStrictTail_zero_projection p _ v hv]
  change _ - (2 * (nonpositiveMixedTriangle p : K[X]).eval (1 / 4) +
    (nonpositiveMixedTriangle p : K[X]).eval 4) = _
  rw [nonpositiveMixedTriangle_weighted p hp]
  simp only [map_mul, WPFiniteJWeightedResidue.inversion_eval,
    LaurentPolynomial.eval₂_toLaurent, eval₂_id]
  simp only [Units.val_inv_eq_inv_val, hv, inv_inv]
  simp only [one_div]
  ring

end WPFieldAssembly.ActualBpairContraction
