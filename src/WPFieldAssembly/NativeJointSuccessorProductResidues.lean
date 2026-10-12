import WPFieldAssembly.NativeJointSuccessorMixedPrimitive

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPFiniteLaurentDifferential
open WPFieldAssembly.ActualSimplePoleResidue
open WPFieldAssembly.ActualBpairContraction
open WPFieldAssembly.NativeJointSuccessorMixedPrimitive

namespace WPFieldAssembly.NativeJointSuccessorProductResidues

variable {K : Type*} [Field K]
set_option maxHeartbeats 2400000

/-- The entire original product with the numerator of dlogV retained. -/
noncomputable def Tprod (p : ℕ) : K :=
  originPole ((originalEven p).toLaurent * invert (originalEven p).toLaurent *
    (33 - 12 * T 1))

/-- The entire original shifted even product over the same Abar. -/
noncomputable def Uprod (p : ℕ) : K :=
  originPole ((originalEven p).toLaurent *
    WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
    T (-(((p - 1) / 2 : ℕ) : ℤ)))

private theorem trunc_shift_minus_one (F : K[T;T⁻¹]) :
    trunc (T (-1) * F) = (trunc F).divX := by
  ext j
  rw [WPFiniteJWeightedResidue.trunc_coeff, coeff_divX,
    WPFiniteJWeightedResidue.trunc_coeff]
  have hs := WPFiniteJCarrier.shifted_coeff (1 : K) (-1) (j : ℤ) F
  simp only [map_one, one_mul] at hs
  rw [hs]
  congr 1

/-- Every negative coefficient contributes to the original logarithmic residue. -/
theorem dlogV_residue_whole (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p)
    (F : K[T;T⁻¹]) :
    originPole ((33 - 12 * T 1) * F) =
      -(trunc (invert F)).eval (1 / 4) - 2 * (trunc (invert F)).eval 4 +
        3 * (invert F).coeff 0 := by
  let P : K[X] := trunc (invert F)
  have ha := congrArg (fun Q : K[X] => Q.eval (1 / 4)) (X_mul_divX_add P)
  have hb := congrArg (fun Q : K[X] => Q.eval 4) (X_mul_divX_add P)
  simp only [eval_add, eval_mul, eval_X, eval_C] at ha hb
  have he : (33 - 12 * T 1) * F =
      LaurentPolynomial.C (33 : K) * F - LaurentPolynomial.C (12 : K) * (T 1 * F) := by
    simp only [map_ofNat]
    ring
  rw [he, originPole_sub, originPole_C_mul, originPole_C_mul,
    originPole_trunc_inverse, originPole_trunc_inverse, map_mul, invert_T,
    trunc_shift_minus_one]
  change (33 : K) * ((P.eval (1 / 4) - P.eval 4) / 15) -
    (12 : K) * ((P.divX.eval (1 / 4) - P.divX.eval 4) / 15) =
      -P.eval (1 / 4) - 2 * P.eval 4 + 3 * (invert F).coeff 0
  have h0 : P.coeff 0 = (invert F).coeff 0 := rfl
  rw [← h0]
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h15 : (15 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 15
    (Finset.mem_Ico.mpr (by omega))
  linear_combination (norm := (field_simp [h3, h4, h5, h15]; ring))
    -(16 / 5 : K) * ha + (1 / 5 : K) * hb

private theorem Dstar_product_pole (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    originPole ((33 - 12 * T 1) *
      ((Dstar p).toLaurent * invert (Dstar p).toLaurent)) =
      -9 * ((Dstar p : K[X]).eval (1 / 4) + (Dstar p).eval 4) ^ 2 / 10 +
        (Dstar p : K[X]).eval (1 / 4) ^ 2 / 2 + (Dstar p).eval 4 ^ 2 -
        3 * (Dstar p).coeff 0 ^ 2 / 2 := by
  let F : K[T;T⁻¹] := (Dstar p).toLaurent * invert (Dstar p).toLaurent
  have hinv : invert F = F := by
    dsimp only [F]
    rw [map_mul, involutive_invert]
    ring
  have hpositive := Dstar_reciprocal_product_positive (K := K) p hp
  have htrunc : trunc F = Polynomial.C (F.coeff 0) +
      Polynomial.C (1 / 2 : K) *
        (branchSquare p - Dstar p ^ 2 + Polynomial.C ((Dstar p : K[X]).coeff 0 ^ 2)) := by
    linear_combination hpositive
  obtain ⟨ha, hb⟩ := branchSquare_endpoints (K := K) p hp
  change originPole ((33 - 12 * T 1) * F) = _
  rw [dlogV_residue_whole p hp]
  simp only [hinv, htrunc, eval_add, eval_mul, eval_sub, eval_pow, eval_C, ha, hb]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  field_simp [h2, h5, h10]
  ring

theorem Tprod_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    Tprod (K := K) p = -9 * (WPFiniteNC122.h p) ^ 2 / 40 +
      (originalEven p : K[X]).eval 4 ^ 2 + (originalEven p).eval (1 / 4) ^ 2 / 2 -
      3 * (originalEven p).eval 0 ^ 2 / 2 := by
  have hE : (originalEven p : K[X]).toLaurent =
      LaurentPolynomial.C (-3 : K) * (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  have he : (originalEven p : K[X]).toLaurent * invert (originalEven p).toLaurent *
      (33 - 12 * T 1) = LaurentPolynomial.C (9 : K) *
        ((33 - 12 * T 1) * ((Dstar p).toLaurent * invert (Dstar p).toLaurent)) := by
    simp only [hE, map_mul, map_neg, map_ofNat]
    ring
  rw [Tprod, he, originPole_C_mul, Dstar_product_pole p hp]
  obtain ⟨ha, hb⟩ := Dstar_endpoints (K := K) p hp
  simp only [originalEven, eval_mul, eval_neg, eval_C, ← coeff_zero_eq_eval_zero, ha, hb]
  have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
    (Finset.mem_Ico.mpr (by omega))
  have h10 : (10 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 10
    (Finset.mem_Ico.mpr (by omega))
  have h40 : (40 : K) ≠ 0 := by
    rw [show (40 : K) = 2 ^ 3 * 5 by ring]
    exact mul_ne_zero (pow_ne_zero 3 h2) h5
  field_simp [h2, h3, h5, h6, h10, h40]
  ring

private theorem trunc_toLaurent_nonnegative (F : K[T;T⁻¹]) (j : ℤ) (hj : 0 ≤ j) :
    (trunc F).toLaurent.coeff j = F.coeff j := by
  have hc : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj
  rw [← hc, WPFiniteJCarrier.toLaurent_coeff_nat, WPFiniteJWeightedResidue.trunc_coeff, hc]

private theorem whole_trunc_decomposition (F : K[T;T⁻¹]) :
    F = (trunc F).toLaurent + invert (trunc (invert F)).toLaurent -
      LaurentPolynomial.C (F.coeff 0) := by
  ext j
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
    Finsupp.add_apply, Finsupp.sub_apply, invert_apply, LaurentPolynomial.C_apply]
  by_cases hj0 : j = 0
  · subst j
    rw [neg_zero, trunc_toLaurent_nonnegative _ _ le_rfl,
      trunc_toLaurent_nonnegative _ _ le_rfl, invert_apply, neg_zero, if_pos rfl]
    ring
  · rw [if_neg hj0]
    by_cases hj : 0 ≤ j
    · rw [trunc_toLaurent_nonnegative _ _ hj,
        WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega))]
      ring
    · rw [WPFiniteJCarrier.toLaurent_coeff_outside _ _ (Or.inl (by omega)),
        trunc_toLaurent_nonnegative _ _ (by omega), invert_apply, neg_neg]
      ring

/-- Inversion changes the full origin residue by the actual rational endpoint difference. -/
theorem originPole_inversion_balance (F : K[T;T⁻¹]) (v : Kˣ) (hv : (v : K) = 4) :
    originPole (invert F) = originPole F +
      (LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ F -
        LaurentPolynomial.eval₂ (RingHom.id K) v F) / 15 := by
  have ha := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹)
    (whole_trunc_decomposition F)
  have hb := congrArg (LaurentPolynomial.eval₂ (RingHom.id K) v)
    (whole_trunc_decomposition F)
  simp only [map_add, map_sub, WPFiniteJWeightedResidue.inversion_eval,
    LaurentPolynomial.eval₂_toLaurent, eval₂_id, LaurentPolynomial.eval₂_C,
    RingHom.id_apply, Units.val_inv_eq_inv_val, hv, inv_inv, ← one_div (4 : K)] at ha hb
  simp only [originPole_trunc_inverse, involutive_invert F]
  linear_combination (norm := (simp only [div_eq_mul_inv]; ring))
    -(15 : K)⁻¹ * (ha - hb)

private theorem squaredCoordinate_ends (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    (WPFiniteWSource.squaredCoordinate : K[X]).eval (1 / 4) = 1 / 4 ∧
      (WPFiniteWSource.squaredCoordinate : K[X]).eval 4 = 1 := by
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
    (Finset.mem_Ico.mpr (by omega))
  simp only [WPFiniteWSource.squaredCoordinate, eval_mul, eval_C, eval_add, eval_X, eval_one]
  constructor <;> field_simp [h4, h5] <;> ring

theorem Uprod_value (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 19 ≤ p) :
    Uprod (K := K) p =
      ((originalEven p : K[X]).eval 4 - (originalEven p).eval (1 / 4)) / 15 -
        WPFiniteNC122.h p / 50 := by
  let S : K[T;T⁻¹] := WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2)
  let F : K[T;T⁻¹] := S * invert (originalEven p).toLaurent
  have hE : (originalEven p : K[X]).toLaurent =
      LaurentPolynomial.C (-3 : K) * (Dstar p).toLaurent := by
    simp only [originalEven, map_mul, map_neg, map_ofNat]
  have hpositive : originPole (S * (originalEven p).toLaurent) = 0 := by
    change originPole (WPFiniteWSource.squaredCoordinate.toLaurent ^ ((p - 1) / 2) *
      (originalEven p : K[X]).toLaurent) = 0
    rw [← map_pow, ← map_mul, originPole_polynomial]
  have hsplit : F = LaurentPolynomial.C (-3 : K) * (S * Dsym p) -
      S * (originalEven p).toLaurent := by
    dsimp only [F]
    simp only [Dsym, hE, map_mul, map_neg, map_ofNat]
    ring
  have hpole : originPole F = -WPFiniteNC122.h p / 50 := by
    rw [hsplit, originPole_sub, originPole_C_mul, hpositive, sub_zero]
    dsimp only [S]
    rw [Dsym_metric_pole p hp]
    obtain ⟨ha, hb⟩ := Dstar_endpoints (K := K) p hp
    rw [ha, hb]
    have h2 : (2 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
      (Finset.mem_Ico.mpr (by omega))
    have h3 : (3 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 3
      (Finset.mem_Ico.mpr (by omega))
    have h5 : (5 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 5
      (Finset.mem_Ico.mpr (by omega))
    have h6 : (6 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 6
      (Finset.mem_Ico.mpr (by omega))
    have h25 : (25 : K) ≠ 0 := by
      rw [show (25 : K) = 5 ^ 2 by ring]
      exact pow_ne_zero 2 h5
    have h50 : (50 : K) ≠ 0 := by
      rw [show (50 : K) = 2 * 5 ^ 2 by ring]
      exact mul_ne_zero h2 (pow_ne_zero 2 h5)
    field_simp [h2, h3, h5, h6, h25, h50]
    ring
  have hinv : invert F = (originalEven p).toLaurent * S *
      T (-(((p - 1) / 2 : ℕ) : ℤ)) := by
    dsimp only [F, S]
    rw [map_mul, involutive_invert, WPFiniteZSource.invert_squared_power p]
    ring
  have h4 : (4 : K) ≠ 0 := WPFiniteField.denominator_ne_zero p 4
    (Finset.mem_Ico.mpr (by omega))
  let v : Kˣ := Units.mk0 4 h4
  have hv : (v : K) = 4 := rfl
  obtain ⟨hsa, hsb⟩ := squaredCoordinate_ends (K := K) p hp
  have hquarter : (1 / 4 : K) ^ ((p - 1) / 2) = 1 := by
    rw [one_div, inv_pow, WPFiniteWSource.four_half_power p hp, inv_one]
  have hFa : LaurentPolynomial.eval₂ (RingHom.id K) v⁻¹ F =
      (originalEven p : K[X]).eval 4 := by
    dsimp only [F, S]
    simp only [map_mul, map_pow, WPFiniteJWeightedResidue.inversion_eval,
      LaurentPolynomial.eval₂_toLaurent, eval₂_id, Units.val_inv_eq_inv_val,
      hv, inv_inv, ← one_div (4 : K), hsa, hquarter, one_mul]
  have hFb : LaurentPolynomial.eval₂ (RingHom.id K) v F =
      (originalEven p : K[X]).eval (1 / 4) := by
    dsimp only [F, S]
    simp only [map_mul, map_pow, WPFiniteJWeightedResidue.inversion_eval,
      LaurentPolynomial.eval₂_toLaurent, eval₂_id, Units.val_inv_eq_inv_val,
      hv, ← one_div (4 : K), hsb, one_pow, one_mul]
  have hbalance := originPole_inversion_balance F v hv
  rw [hinv, hpole, hFa, hFb] at hbalance
  dsimp only [Uprod]
  change originPole ((originalEven p).toLaurent * S *
    T (-(((p - 1) / 2 : ℕ) : ℤ))) = _
  linear_combination hbalance

end WPFieldAssembly.NativeJointSuccessorProductResidues
