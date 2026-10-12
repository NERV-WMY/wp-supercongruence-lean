import WPActualCanonicalSource

open scoped BigOperators Polynomial LaurentPolynomial
open LaurentPolynomial WPRationalCartier WPQuadraticRationalCartier
open WPNC67ActualSources WPActualCanonicalSource WPCartierPoleProjection
open WPActualEtaFieldCutoff WPActualEtaPrimitive
open WPActualEtaIntegration

namespace WPActualCanonicalProjection

variable (p : ℕ) [Fact p.Prime]

theorem fieldVx_normalform : fieldVx p =
    C (1 / 125) * (4 * T 1 - 1) ^ 2 * (4 - T 1) := by
  have hc : (((1 / 125 : ℚ) : ZMod p)) = 1 / (125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 125)
  simp only [fieldVx, WPHasseIntegralTransport.fieldV, map_mul, map_sub,
    map_pow, Polynomial.toLaurent_C, Polynomial.toLaurent_X, map_ofNat, map_one, hc]

theorem fieldDerivativeVx_normalform : fieldDerivativeVx p =
    C (3 / 125) * (4 * T 1 - 1) * (11 - 4 * T 1) := by
  have hc : (((1 / 125 : ℚ) : ZMod p)) = 1 / (125 : ZMod p) := by
    simpa only [one_div, Nat.cast_ofNat] using (Rat.cast_inv_nat (α := ZMod p) 125)
  have hd : (WPHasseIntegralTransport.fieldV p).derivative =
      Polynomial.C (3 / 125) * (4 * Polynomial.X - 1) * (11 - 4 * Polynomial.X) := by
    rw [show (3 / 125 : ZMod p) = (1 / 125) * 3 by ring, Polynomial.C_mul]
    simp only [WPHasseIntegralTransport.fieldV, hc]
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [map_ofNat]
    ring
  rw [fieldDerivativeVx, hd]
  simp only [map_mul, map_sub, Polynomial.toLaurent_C, Polynomial.toLaurent_X,
    map_ofNat, map_one]

theorem square_fieldVx : squareSubstitute p (fieldVx p) = actualV p := by
  rw [fieldVx_normalform]
  simp only [map_mul, map_sub, map_pow, squareSubstitute_C, squareSubstitute_T,
    map_ofNat, map_one, Int.reduceMul, actualV]

private theorem field_units (hp : 19 ≤ p) :
    (2 : RatFunc (ZMod p)) ≠ 0 ∧ (4 : RatFunc (ZMod p)) ≠ 0 ∧
      (125 : RatFunc (ZMod p)) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 2) hd
    omega
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 5 p).mp h
    have := Nat.le_of_dvd (by omega : 0 < 5) hd
    omega
  have hc2 : (2 : RatFunc (ZMod p)) ≠ 0 := by
    have h : RatFunc.C (2 : ZMod p) ≠ 0 := (map_ne_zero RatFunc.C).mpr h2
    simpa only [map_ofNat] using h
  have hc5 : (5 : RatFunc (ZMod p)) ≠ 0 := by
    have h : RatFunc.C (5 : ZMod p) ≠ 0 := (map_ne_zero RatFunc.C).mpr h5
    simpa only [map_ofNat] using h
  have hc4 : (4 : RatFunc (ZMod p)) ≠ 0 := by
    convert pow_ne_zero 2 hc2 using 1; norm_num
  have hc125 : (125 : RatFunc (ZMod p)) ≠ 0 := by
    convert pow_ne_zero 3 hc5 using 1; norm_num
  exact ⟨hc2, hc4, hc125⟩

private theorem pole_ne_zero (a : ZMod p) :
    (RatFunc.X - RatFunc.C a : RatFunc (ZMod p)) ≠ 0 := by
  have h := RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero a)
  simpa using h

theorem fieldVx_evaluate : evaluate p (fieldVx p) =
    (4 * RatFunc.X - 1) ^ 2 * (4 - RatFunc.X) / 125 := by
  rw [fieldVx_normalform]
  simp only [map_mul, map_sub, map_pow, map_ofNat, map_one,
    evaluate_C, evaluate_T, map_div₀, zpow_one]
  ring

theorem fieldDerivativeVx_evaluate : evaluate p (fieldDerivativeVx p) =
    3 * (4 * RatFunc.X - 1) * (11 - 4 * RatFunc.X) / 125 := by
  rw [fieldDerivativeVx_normalform]
  simp only [map_mul, map_sub, map_ofNat, map_one, evaluate_C, evaluate_T, map_div₀, zpow_one]
  ring

theorem fieldVx_evaluate_ne_zero (hp : 19 ≤ p) : evaluate p (fieldVx p) ≠ 0 := by
  obtain ⟨_, h4, h125⟩ := field_units p hp
  have ha := pole_ne_zero p (1 / 4)
  have hb := pole_ne_zero p 4
  have ha' : (4 * RatFunc.X - 1 : RatFunc (ZMod p)) ≠ 0 := by
    have he : (4 * RatFunc.X - 1 : RatFunc (ZMod p)) =
        4 * (RatFunc.X - RatFunc.C (1 / 4 : ZMod p)) := by
      simp only [map_div₀, map_one, map_ofNat]
      field_simp [h4]
    rw [he]
    exact mul_ne_zero h4 ha
  have hb' : (4 - RatFunc.X : RatFunc (ZMod p)) ≠ 0 := by
    simpa only [map_ofNat, neg_sub] using neg_ne_zero.mpr hb
  rw [fieldVx_evaluate]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ ha') hb') h125

/-- The logarithmic derivative is obtained from the literal cubic and its derivative. -/
theorem literal_logarithmicX (hp : 19 ≤ p) :
    logarithmicX p =
      evaluate p (C 2 * T 1 * fieldDerivativeVx p - fieldVx p) /
        evaluate p (C 2 * T 1 * fieldVx p) := by
  obtain ⟨h2, h4, h125⟩ := field_units p hp
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have ha := pole_ne_zero p (1 / 4)
  have hb := pole_ne_zero p 4
  have ha' : (-1 + RatFunc.X * 4 : RatFunc (ZMod p)) ≠ 0 := by
    have h := mul_ne_zero h4 ha
    convert h using 1
    simp only [map_div₀, map_one, map_ofNat]
    field_simp [h4]
    ring
  have hD : evaluate p (C 2 * T 1 * fieldVx p) ≠ 0 := by
    simp only [map_mul, evaluate_T, map_ofNat, zpow_one]
    exact mul_ne_zero (mul_ne_zero h2 hx) (fieldVx_evaluate_ne_zero p hp)
  apply (eq_div_iff hD).mpr
  simp only [logarithmicX, map_sub, map_mul, evaluate_T,
    map_ofNat, zpow_one, fieldVx_evaluate, fieldDerivativeVx_evaluate,
    map_div₀, map_one]
  simp only [map_div₀, map_one, map_ofNat] at ha hb
  field_simp [h2, h4, h125, hx, ha, ha', hb]
  ring_nf
  field_simp [ha']
  ring

theorem actualV_evaluate_ne_zero (hp : 19 ≤ p) : evaluate p (actualV p) ≠ 0 := by
  intro h
  have hz : squareSubstitute p (fieldVx p) = 0 := by
    apply evaluate_injective p
    simpa only [square_fieldVx, map_zero] using h
  have hV : fieldVx p = 0 := squareSubstitute_injective p (by simpa using hz)
  exact fieldVx_evaluate_ne_zero p hp (by rw [hV, map_zero])

/-- Whole canonical differential equality; every signed coefficient of A is retained. -/
theorem full_canonical_source (hp : 19 ≤ p) (A : (ZMod p)[T;T⁻¹]) :
    evaluate p (fieldCanonicalDensity p * squareSubstitute p A) =
      evaluate p (actualS p) ^ p *
        quadraticRational p (evaluate p A * logarithmicX p) := by
  obtain ⟨h2, _, _⟩ := field_units p hp
  have hx : (RatFunc.X : RatFunc (ZMod p)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have hV := fieldVx_evaluate_ne_zero p hp
  have hsV := actualV_evaluate_ne_zero p hp
  have hD : evaluate p (C 2 * T 1 * fieldVx p) ≠ 0 := by
    simp only [map_mul, evaluate_T, map_ofNat, zpow_one]
    exact mul_ne_zero (mul_ne_zero h2 hx) hV
  have hf : evaluate p A * logarithmicX p =
      evaluate p (A * (C 2 * T 1 * fieldDerivativeVx p - fieldVx p)) /
        evaluate p (C 2 * T 1 * fieldVx p) := by
    rw [literal_logarithmicX p hp]
    simp only [map_mul, mul_div_assoc]
  rw [hf, quadraticRational_fraction p _ _ hD, actualS_evaluate,
    fieldCanonicalDensity]
  have hexp : p = (p - 1) + 1 := by omega
  simp only [map_mul, map_sub, map_pow, squareSubstitute_T,
    map_ofNat, square_fieldVx, evaluate_T, Int.reduceMul, zpow_one]
  rw [show (-(p : ℤ) - 1) = -((p : ℤ) + 1) by ring,
    zpow_neg, zpow_add₀ hx, zpow_natCast, zpow_one]
  rw [div_pow]
  have hpcast : (evaluate p (actualV p) ^ p : RatFunc (ZMod p)) =
      evaluate p (actualV p) ^ (p - 1) * evaluate p (actualV p) := by
    exact (congrArg (fun n => evaluate p (actualV p) ^ n) hexp).trans (pow_succ _ _)
  rw [hpcast]
  norm_num only [zpow_ofNat]
  field_simp [h2, hx, hsV]

theorem literal_canonicalPeriod_NC67 (hp : 19 ≤ p) :
    (canonicalPeriod p ((p - 1) / 2) (p - 1 - p / 6) : ZMod p) =
      (1044 / 625) * valueAt p (literalFieldAeta p hp) (1 / 4) -
        (828 / 625) * valueAt p (literalFieldAeta p hp) 4 +
        (432 / 625) * (-2 * negativeValue p (literalFieldAeta p hp) (1 / 4) -
          negativeValue p (literalFieldAeta p hp) 4) +
        (6102 / 4375) * (8 * highValue p (literalFieldAeta p hp) (1 / 4) +
          highValue p (literalFieldAeta p hp) 4 / 4) := by
  rw [literal_canonicalPeriod_residue p hp]
  exact full_band_primitive_evaluation p hp (literalFieldAeta p hp) _
    (fun j hj => literal_field_Aeta_full_band p hp j (Finsupp.mem_support_iff.mp hj))
    (literal_field_Aeta_NC63 p hp).2.1 (literal_field_Aeta_NC63 p hp).2.2
    (full_canonical_source p hp (literalFieldAeta p hp))

end WPActualCanonicalProjection
