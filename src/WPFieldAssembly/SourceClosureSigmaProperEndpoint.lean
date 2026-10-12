import WPFieldAssembly.SourceClosureSigmaProperJ

open scoped Polynomial LaurentPolynomial
open Polynomial LaurentPolynomial WPActualChiSource WPPIntegralReduction
  WPActualRankTwoHatLift WPFieldAssembly.SourceClosureSigmaProperJ

namespace WPFieldAssembly.SourceClosureSigmaProperEndpoint

set_option maxHeartbeats 1500000

/- The rational endpoints are subtracted in the original proper carrier.
Only afterwards is its genuine p-multiple divided and reduced. -/

theorem eval₂_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) (F : R[T;T⁻¹]) :
    f (LaurentPolynomial.eval₂ (RingHom.id R) u F) =
      LaurentPolynomial.eval₂ (RingHom.id S) (Units.map f.toMonoidHom u)
        (coefficientMap f F) := by
  induction F using LaurentPolynomial.induction_on' with
  | add F G hF hG => simp only [_root_.map_add, hF, hG]
  | C_mul_T n c =>
    rw [coefficientMap_monomial, LaurentPolynomial.eval₂_C_mul_T,
      LaurentPolynomial.eval₂_C_mul_T]
    simp only [RingHom.id_apply, _root_.map_mul]
    congr 1
    have hu := map_zpow (Units.map f.toMonoidHom) u n
    exact congrArg (fun v : Sˣ => (v : S)) hu

noncomputable def endSym {R : Type*} [CommRing R] (u : Rˣ)
    (F : R[T;T⁻¹]) : R[T;T⁻¹] :=
  F + invert F - LaurentPolynomial.C (LaurentPolynomial.eval₂ (RingHom.id R) u⁻¹ F) -
    LaurentPolynomial.C (LaurentPolynomial.eval₂ (RingHom.id R) u F)

theorem endSym_add {R : Type*} [CommRing R] (u : Rˣ) (F G : R[T;T⁻¹]) :
    endSym u (F + G) = endSym u F + endSym u G := by
  simp only [endSym, _root_.map_add]
  ring

theorem endSym_sub {R : Type*} [CommRing R] (u : Rˣ) (F G : R[T;T⁻¹]) :
    endSym u (F - G) = endSym u F - endSym u G := by
  simp only [endSym, _root_.map_sub]
  ring

theorem endSym_C_mul {R : Type*} [CommRing R] (u : Rˣ) (c : R) (F : R[T;T⁻¹]) :
    endSym u (LaurentPolynomial.C c * F) = LaurentPolynomial.C c * endSym u F := by
  simp only [endSym, _root_.map_mul, LaurentPolynomial.invert_C,
    LaurentPolynomial.eval₂_C, RingHom.id_apply]
  ring

theorem endSym_C {R : Type*} [CommRing R] (u : Rˣ) (c : R) :
    endSym u (LaurentPolynomial.C c) = 0 := by
  simp only [endSym, LaurentPolynomial.invert_C, LaurentPolynomial.eval₂_C,
    RingHom.id_apply]
  ring

theorem endSym_derivative {R : Type*} [Field R] (u : Rˣ) (F : R[T;T⁻¹]) :
    WPFiniteLaurentDifferential.D (endSym u F) =
      WPFiniteLaurentDifferential.D F - T (-2) *
        invert (WPFiniteLaurentDifferential.D F) := by
  rw [endSym, _root_.map_sub, _root_.map_sub, _root_.map_add, WPFiniteLaurentDifferential.D_C,
    WPFiniteLaurentDifferential.D_C, sub_zero, sub_zero,
    WPFiniteLaurentDifferential.D_invert]
  ring

theorem endSym_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Rˣ) (F : R[T;T⁻¹]) :
    coefficientMap f (endSym u F) = endSym (Units.map f.toMonoidHom u)
      (coefficientMap f F) := by
  simp only [endSym, _root_.map_sub, _root_.map_add, coefficientMap_invert,
    coefficientMap_C, eval₂_map f u⁻¹ F, eval₂_map f u F, _root_.map_inv]

noncomputable def fourUnitI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (integralRationals p)ˣ :=
  { val := 4
    inv := smallIntegralInverse p 4
    val_inv := by
      apply Subtype.ext
      change (4 : ℚ) * (smallIntegralInverse p 4).val = 1
      rw [smallIntegralInverse_value p 4 (by omega) (by omega)]
      norm_num
    inv_val := by
      apply Subtype.ext
      change (smallIntegralInverse p 4).val * (4 : ℚ) = 1
      rw [smallIntegralInverse_value p 4 (by omega) (by omega)]
      norm_num }

noncomputable def fourUnitQ : ℚˣ := Units.mk0 4 (by norm_num)

noncomputable def fourUnitField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) : (ZMod p)ˣ :=
  Units.mk0 4 (WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega))

theorem fourUnitI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Units.map (integralRationals p).subtype.toMonoidHom (fourUnitI p hp) = fourUnitQ := by
  apply Units.ext
  rfl

theorem fourUnitI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    Units.map (residueHom p).toMonoidHom (fourUnitI p hp) = fourUnitField p hp := by
  apply Units.ext
  change residueHom p (4 : integralRationals p) = (4 : ZMod p)
  exact _root_.map_ofNat (residueHom p) 4

noncomputable def properEndSymI (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p)[T;T⁻¹] := endSym (fourUnitI p hp) (properJI p)

noncomputable def properEndSymQ (p : ℕ) : ℚ[T;T⁻¹] := endSym fourUnitQ (properJQ p)

noncomputable def properEndSymField (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (ZMod p)[T;T⁻¹] := endSym (fourUnitField p hp) (properJField p)

/-- The original rational proper derivative retains its uncomputed positive-p slot. -/
theorem properEndSymQ_derivative (p : ℕ) [Fact p.Prime] :
    WPFiniteLaurentDifferential.D (properEndSymQ p) =
      properDensityQ p - T (-2) * invert (properDensityQ p) -
        LaurentPolynomial.C ((properDensityQ p).coeff ((p : ℤ) - 1)) *
          (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  have ht : (T (-2) : ℚ[T;T⁻¹]) * T 1 = T (-1) := by
    rw [← T_add]
    norm_num
  have hpT : (T (-2) : ℚ[T;T⁻¹]) * T (-((p : ℤ) - 1)) =
      T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
    omega
  rw [properEndSymQ, endSym_derivative, properJQ_source]
  simp only [_root_.map_sub, _root_.map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  simp only [neg_neg]
  linear_combination
    LaurentPolynomial.C ((properDensityQ p).coeff (-1)) * ht +
      LaurentPolynomial.C ((properDensityQ p).coeff ((p : ℤ) - 1)) * hpT

theorem properEndSymI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype (properEndSymI p hp) = properEndSymQ p := by
  rw [properEndSymI, endSym_map, fourUnitI_value p hp, properJI_value p hp]
  rfl

theorem properEndSymI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p) (properEndSymI p hp) = properEndSymField p hp := by
  rw [properEndSymI, endSym_map, fourUnitI_field p hp, properJI_field p hp]
  rfl

theorem properJField_endpoints (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
        (properJField p) = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
        (properJField p) = 0 := by
  have h4 : (4 : ZMod p) ≠ 0 :=
    WPActualGaussProper.small_cast_ne_zero p 4 (by omega) (by omega)
  have hLP : (WPFiniteAffineLog.LP p : (ZMod p)[X]).eval 1 = 0 := by
    rw [WPFiniteAffineLog.LP_eval_eq]
    exact WPFiniteInversion.ell_one_eq_zero p (by omega)
  have hv : (fourUnitField p hp : ZMod p) = 4 := rfl
  have hfourp : (4 : ZMod p) ^ p = 4 := ZMod.pow_card _
  have hvi : (((fourUnitField p hp)⁻¹ : (ZMod p)ˣ) : ZMod p) = (4 : ZMod p)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hv]
  have hTa : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
      (T (-(p : ℤ))) = (4 : ZMod p) := by
    rw [LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, hvi,
      zpow_neg, zpow_natCast, inv_pow, inv_inv, hfourp]
  have hTb : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)
      (T (-(p : ℤ))) = (4 : ZMod p)⁻¹ := by
    rw [LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, hv,
      zpow_neg, zpow_natCast, hfourp]
  have hLa : LaurentPolynomial.eval₂ (RingHom.id (ZMod p)) (fourUnitField p hp)⁻¹
      (logFourField p).toLaurent = 0 := by
    simp only [logFourField, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
      Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      hvi, mul_inv_cancel₀ h4, hLP]
  constructor
  · simp only [properJField, _root_.map_mul, _root_.map_sub,
      LaurentPolynomial.eval₂_C, RingHom.id_apply, hTa, hLa, mul_zero]
  · simp only [properJField, _root_.map_mul, _root_.map_sub, LaurentPolynomial.eval₂_C,
      RingHom.id_apply, hTb, one_div, sub_self, mul_zero, zero_mul]

theorem properEndSymField_identification (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    properEndSymField p hp = properJField p + invert (properJField p) := by
  obtain ⟨ha, hb⟩ := properJField_endpoints p hp
  rw [properEndSymField, endSym, ha, hb, _root_.map_zero, sub_zero, sub_zero]

theorem properEndSymField_derivative (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    WPFiniteLaurentDifferential.D (properEndSymField p hp) =
      properDensityField p - T (-2) * invert (properDensityField p) +
        LaurentPolynomial.C (2 / 15 : ZMod p) *
          (T ((p : ℤ) - 1) - T (-(p : ℤ) - 1)) := by
  have ht : (T (-2) : (ZMod p)[T;T⁻¹]) * T 1 = T (-1) := by
    rw [← T_add]
    norm_num
  have hpT : (T (-2) : (ZMod p)[T;T⁻¹]) * T (-((p : ℤ) - 1)) =
      T (-(p : ℤ) - 1) := by
    rw [← T_add]
    congr 1
    omega
  rw [properEndSymField_identification p hp, _root_.map_add,
    WPFiniteLaurentDifferential.D_invert, properJField_derivative p hp]
  simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, LaurentPolynomial.invert_C,
    LaurentPolynomial.invert_T, neg_neg]
  linear_combination
    LaurentPolynomial.C (8 / 15 : ZMod p) * ht -
      LaurentPolynomial.C (2 / 15 : ZMod p) * hpT

noncomputable def properCarryQ (p : ℕ) : ℚ :=
  (1 / 5 : ℚ) ^ (2 * (p - 1)) * (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1)

noncomputable def properCarryDigitI (p : ℕ) [Fact p.Prime] : integralRationals p :=
  -(smallIntegralInverse p 5) ^ (2 * (p - 1)) *
    (WPFiniteInversion.integerFermatQuotient p 2 : integralRationals p) *
    (smallIntegralInverse p 4) ^ ((p - 1) / 2)

theorem properCarryDigitI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (integralRationals p).subtype (properCarryDigitI p) = properCarryQ p / (p : ℚ) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hA : (4 : ℚ) ^ ((p - 1) / 2) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := WPFiniteField.denominator_ne_zero p 2
    (Finset.mem_Ico.mpr (by omega))
  have hq := WPFiniteInversion.integerFermatQuotient_mul p 2 (by simpa using h2)
  have hqQ : (WPFiniteInversion.integerFermatQuotient p 2 : ℚ) * (p : ℚ) =
      (2 : ℚ) ^ (p - 1) - 1 := by exact_mod_cast hq
  have hn : 2 * ((p - 1) / 2) = p - 1 := by
    have ht := WPFiniteWSource.half_exponent p hp
    omega
  have hfour : (4 : ℚ) ^ ((p - 1) / 2) = (2 : ℚ) ^ (p - 1) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, hn]
  rw [← hfour] at hqQ
  have hdiv : -(WPFiniteInversion.integerFermatQuotient p 2 : ℚ) *
      ((4 : ℚ) ^ ((p - 1) / 2))⁻¹ =
        (((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) / (p : ℚ) := by
    field_simp [hpq, hA]
    linear_combination -hqQ
  have h4v : (integralRationals p).subtype (smallIntegralInverse p 4) = (1 / 4 : ℚ) :=
    smallIntegralInverse_value p 4 (by omega) (by omega)
  have h5v : (integralRationals p).subtype (smallIntegralInverse p 5) = (1 / 5 : ℚ) :=
    smallIntegralInverse_value p 5 (by omega) (by omega)
  have h4pow : (1 / 4 : ℚ) ^ ((p - 1) / 2) =
      ((4 : ℚ) ^ ((p - 1) / 2))⁻¹ := by rw [one_div, inv_pow]
  simp only [properCarryDigitI, _root_.map_mul, _root_.map_neg, _root_.map_pow, _root_.map_intCast,
    h4v, h5v, properCarryQ]
  rw [h4pow]
  calc
    _ = (1 / 5 : ℚ) ^ (2 * (p - 1)) *
        (-(WPFiniteInversion.integerFermatQuotient p 2 : ℚ) *
          ((4 : ℚ) ^ ((p - 1) / 2))⁻¹) := by ring
    _ = (1 / 5 : ℚ) ^ (2 * (p - 1)) *
        ((((4 : ℚ) ^ ((p - 1) / 2))⁻¹ - 1) / (p : ℚ)) := by rw [hdiv]
    _ = _ := by ring

theorem properCarryDigitI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    residueHom p (properCarryDigitI p) =
      -(WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) := by
  have h5 : ((5 : ZMod p)⁻¹) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one
      (inv_ne_zero (WPActualGaussProper.small_cast_ne_zero p 5 (by omega) (by omega)))
  have h5two : ((5 : ZMod p)⁻¹) ^ (2 * (p - 1)) = 1 := by
    rw [mul_comm (2 : ℕ), pow_mul, h5, one_pow]
  have h4 : ((4 : ZMod p)⁻¹) ^ ((p - 1) / 2) = 1 := by
    rw [inv_pow, WPFiniteWSource.four_half_power p hp, inv_one]
  simp only [properCarryDigitI, _root_.map_mul, _root_.map_neg, _root_.map_pow, _root_.map_intCast,
    smallIntegralInverse_field p 4 (by omega) (by omega),
    smallIntegralInverse_field p 5 (by omega) (by omega), Nat.cast_ofNat,
    h5two, h4, neg_one_mul, mul_one]

/-- The actual proper term is divided only after retaining its original rational ends. -/
theorem properCarryEndSymI_value (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (integralRationals p).subtype
      (LaurentPolynomial.C (properCarryDigitI p) * properEndSymI p hp) =
        LaurentPolynomial.C (1 / (p : ℚ)) *
          LaurentPolynomial.C (properCarryQ p) * properEndSymQ p := by
  rw [_root_.map_mul, coefficientMap_C, properCarryDigitI_value p hp, properEndSymI_value p hp]
  have hc : (LaurentPolynomial.C (properCarryQ p / (p : ℚ)) : ℚ[T;T⁻¹]) =
      LaurentPolynomial.C (1 / (p : ℚ)) * LaurentPolynomial.C (properCarryQ p) := by
    rw [← _root_.map_mul]
    congr 1
    ring
  rw [hc]

/-- UW16l's full proper first carry, with reflected and endpoint transport proved. -/
theorem properCarryEndSymI_field (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    coefficientMap (residueHom p)
      (LaurentPolynomial.C (properCarryDigitI p) * properEndSymI p hp) =
        -LaurentPolynomial.C (WPFiniteInversion.integerFermatQuotient p 2 : ZMod p) *
          properEndSymField p hp := by
  rw [_root_.map_mul, coefficientMap_C, properCarryDigitI_field p hp, properEndSymI_field p hp,
    _root_.map_neg, neg_mul]

end WPFieldAssembly.SourceClosureSigmaProperEndpoint
