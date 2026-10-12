import WPPIntegralReduction
import WPRationalCartier

open scoped Polynomial LaurentPolynomial
open LaurentPolynomial WPPIntegralReduction WPRationalCartier

namespace WPNC67ProjectionIntegrals

variable (p : ℕ) [Fact p.Prime]

private theorem small_unit (n : ℕ) (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  intro h
  have hd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h
  have hle := Nat.le_of_dvd hn hd
  omega

private theorem denominator_units (hp : 19 ≤ p) :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 ∧ (5 : ZMod p) ≠ 0 ∧
    (7 : ZMod p) ≠ 0 ∧ (8 : ZMod p) ≠ 0 ∧ (9 : ZMod p) ≠ 0 ∧
    (24 : ZMod p) ≠ 0 ∧ (32 : ZMod p) ≠ 0 ∧ (125 : ZMod p) ≠ 0 ∧
    (128 : ZMod p) ≠ 0 ∧ (160 : ZMod p) ≠ 0 ∧ (512 : ZMod p) ≠ 0 ∧
    (625 : ZMod p) ≠ 0 ∧ (896 : ZMod p) ≠ 0 ∧ (4375 : ZMod p) ≠ 0 ∧
    (4608 : ZMod p) ≠ 0 ∧ (8750 : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by simpa using small_unit p 2 (by omega) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by simpa using small_unit p 3 (by omega) (by omega)
  have h5 : (5 : ZMod p) ≠ 0 := by simpa using small_unit p 5 (by omega) (by omega)
  have h7 : (7 : ZMod p) ≠ 0 := by simpa using small_unit p 7 (by omega) (by omega)
  have h8 : (8 : ZMod p) ≠ 0 := by convert pow_ne_zero 3 h2 using 1; norm_num
  have h9 : (9 : ZMod p) ≠ 0 := by convert pow_ne_zero 2 h3 using 1; norm_num
  have h24 : (24 : ZMod p) ≠ 0 := by convert mul_ne_zero h3 h8 using 1; norm_num
  have h32 : (32 : ZMod p) ≠ 0 := by convert pow_ne_zero 5 h2 using 1; norm_num
  have h125 : (125 : ZMod p) ≠ 0 := by convert pow_ne_zero 3 h5 using 1; norm_num
  have h128 : (128 : ZMod p) ≠ 0 := by convert pow_ne_zero 7 h2 using 1; norm_num
  have h160 : (160 : ZMod p) ≠ 0 := by convert mul_ne_zero h5 h32 using 1; norm_num
  have h512 : (512 : ZMod p) ≠ 0 := by convert pow_ne_zero 9 h2 using 1; norm_num
  have h625 : (625 : ZMod p) ≠ 0 := by convert pow_ne_zero 4 h5 using 1; norm_num
  have h896 : (896 : ZMod p) ≠ 0 := by convert mul_ne_zero h7 h128 using 1; norm_num
  have h4375 : (4375 : ZMod p) ≠ 0 := by convert mul_ne_zero h7 h625 using 1; norm_num
  have h4608 : (4608 : ZMod p) ≠ 0 := by convert mul_ne_zero h9 h512 using 1; norm_num
  have h8750 : (8750 : ZMod p) ≠ 0 := by convert mul_ne_zero h2 h4375 using 1; norm_num
  exact ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩

/-- The complete canceled Laurent coefficient for the poleA projection. -/
noncomputable def poleA : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 4 + C (136 / 125) * T 2 + C (-32 / 125) * T 0

/-- The complete canceled Laurent coefficient for the poleB projection. -/
noncomputable def poleB : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 4 + C (16 / 125) * T 2 + C (-2 / 125) * T 0

/-- The complete canceled Laurent coefficient for the logPole projection. -/
noncomputable def logPole : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 4 + C (144 / 125) * T 2 + C (-66 / 125) * T 0 + C (8 / 125) * T (-2)

/-- The complete canceled Laurent coefficient for the constantPole projection. -/
noncomputable def constantPole : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 6 + C (144 / 125) * T 4 + C (-66 / 125) * T 2 + C (8 / 125) * T 0

/-- The complete canceled Laurent coefficient for the resonanceMinus projection. -/
noncomputable def resonanceMinus : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 2 + C (144 / 125) * T 0 + C (-66 / 125) * T (-2) + C (8 / 125) * T (-4)

/-- The complete canceled Laurent coefficient for the resonancePlus projection. -/
noncomputable def resonancePlus : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 6 + C (144 / 125) * T 4 + C (-66 / 125) * T 2 + C (8 / 125) * T 0

/-- The complete canceled Laurent coefficient for the resonanceTwo projection. -/
noncomputable def resonanceTwo : (ZMod p)[T;T⁻¹] :=
  C (-32 / 125) * T 8 + C (144 / 125) * T 6 + C (-66 / 125) * T 4 + C (8 / 125) * T 2

theorem poleA_integral (hp : 19 ≤ p) : fieldPrimitive p (poleA p) = 522 / 625 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [poleA, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem poleB_integral (hp : 19 ≤ p) : fieldPrimitive p (poleB p) = -828 / 625 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [poleB, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem logPole_integral (hp : 19 ≤ p) : fieldPrimitive p (logPole p) = 432 / 625 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [logPole, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem constantPole_integral (hp : 19 ≤ p) : fieldPrimitive p (constantPole p) = 6102 / 4375 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [constantPole, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem resonanceMinus_integral (hp : 19 ≤ p) : fieldPrimitive p (resonanceMinus p) = 54 / 125 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [resonanceMinus, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem resonancePlus_integral (hp : 19 ≤ p) : fieldPrimitive p (resonancePlus p) = 6102 / 4375 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [resonancePlus, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

theorem resonanceTwo_integral (hp : 19 ≤ p) : fieldPrimitive p (resonanceTwo p) = 28809 / 8750 := by
  obtain ⟨h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160, h512,
    h625, h896, h4375, h4608, h8750⟩ := denominator_units p hp
  simp only [resonanceTwo, map_add, fieldPrimitive_monomial, fieldWeight]
  norm_num only [Int.reduceAdd, Int.reduceNeg, Int.cast_ofNat, Int.cast_neg,
    zpow_neg, zpow_natCast]
  field_simp [h2, h3, h5, h7, h8, h9, h24, h32, h125, h128, h160,
    h512, h625, h896, h4375, h4608, h8750]
  ring

end WPNC67ProjectionIntegrals
