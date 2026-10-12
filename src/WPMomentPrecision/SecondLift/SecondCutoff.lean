import WPMomentPrecision.SecondLift.SecondRecurrence

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter WPActualNativeFirstJet
  WPActualNativeSecondJet WPActualNativeJetRecurrence
  WPMomentPrecision.FullNativeTaylor
  WPMomentPrecision.SecondRecurrence

namespace WPMomentPrecision.SecondCutoff

set_option maxHeartbeats 1200000

theorem numerator_divisibility_of_le {R : Type*} [CommRing R]
    (m n : ℕ) (hmn : m ≤ n) : clearedNumerator R m ∣ clearedNumerator R n := by
  unfold clearedNumerator
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono hmn)

theorem upperFactor_low_X_dvd (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (X : (ZMod p)[X]) ∣ upperFactor (ZMod p) (p / 6) := by
  apply X_dvd_iff.mpr
  rw [coeff_zero_eq_eval_zero, upperFactor_origin]
  rcases prime_six_classes p (by omega) with hp1 | hp5
  · have hc : 6 * ((p / 6 : ℕ) : ZMod p) + 1 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hp1
      simpa using h.symm
    rw [hc, mul_zero, zero_mul]
  · have hc : 6 * ((p / 6 : ℕ) : ZMod p) + 5 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) hp5
      simpa using h.symm
    rw [hc, mul_zero]

theorem upperFactor_half_X_dvd (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (X : (ZMod p)[X]) ∣ upperFactor (ZMod p) ((p - 1) / 2) := by
  apply X_dvd_iff.mpr
  rw [coeff_zero_eq_eval_zero, upperFactor_origin]
  have he := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hc : 2 * (((p - 1) / 2 : ℕ) : ZMod p) + 1 = 0 := by
    have h := congrArg (fun n : ℕ => (n : ZMod p)) he
    simpa using h
  rw [hc, zero_mul, zero_mul]

theorem upperFactor_high_X_dvd (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p) :
    (X : (ZMod p)[X]) ∣ upperFactor (ZMod p) (p - 1 - p / 6) := by
  apply X_dvd_iff.mpr
  rw [coeff_zero_eq_eval_zero, upperFactor_origin]
  rcases prime_six_classes p (by omega) with hp1 | hp5
  · have he : 6 * (p - 1 - p / 6) + 5 = 5 * p := by omega
    have hc : 6 * ((p - 1 - p / 6 : ℕ) : ZMod p) + 5 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) he
      simpa using h
    rw [hc, mul_zero]
  · have he : 6 * (p - 1 - p / 6) + 1 = 5 * p := by omega
    have hc : 6 * ((p - 1 - p / 6 : ℕ) : ZMod p) + 1 = 0 := by
      have h := congrArg (fun n : ℕ => (n : ZMod p)) he
      simpa using h
    rw [hc, mul_zero, zero_mul]

/-- Three distinct upper zeros, at d, N and e, retain the actual second cutoff source. -/
theorem actual_native_numerator_triple_zero (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : p - 1 - p / 6 < n) :
    (X : (ZMod p)[X]) ^ 3 ∣ clearedNumerator (ZMod p) n := by
  have hd := Nat.div_mul_le_self p 6
  have hh := WPActualHasseReciprocal.actual_half_exponent p (by omega)
  have hlow : (X : (ZMod p)[X]) ∣ clearedNumerator (ZMod p) (p / 6 + 1) := by
    rw [actual_parameter_numerator_succ]
    exact dvd_mul_of_dvd_right (upperFactor_low_X_dvd p hp) _
  have hhalf : (X : (ZMod p)[X]) ∣ clearedNumerator (ZMod p) ((p - 1) / 2) :=
    dvd_trans hlow (numerator_divisibility_of_le _ _ (by omega))
  have htwo : (X : (ZMod p)[X]) ^ 2 ∣
      clearedNumerator (ZMod p) ((p - 1) / 2 + 1) := by
    rw [actual_parameter_numerator_succ, pow_two]
    exact mul_dvd_mul hhalf (upperFactor_half_X_dvd p hp)
  have hhigh : (X : (ZMod p)[X]) ^ 2 ∣
      clearedNumerator (ZMod p) (p - 1 - p / 6) :=
    dvd_trans htwo (numerator_divisibility_of_le _ _ (by omega))
  have hthree : (X : (ZMod p)[X]) ^ 3 ∣
      clearedNumerator (ZMod p) (p - 1 - p / 6 + 1) := by
    rw [actual_parameter_numerator_succ, show (3 : ℕ) = 2 + 1 by omega, pow_succ]
    exact mul_dvd_mul hhigh (upperFactor_high_X_dvd p hp)
  exact dvd_trans hthree (numerator_divisibility_of_le _ _ (by omega))

/-- The actual Hasse second quotient above e reduces to zero from all three factors. -/
theorem integral_second_jet_tail_zero (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (he : p - 1 - p / 6 < n) :
    residueHom p (integralParameterSecondJet p n (by omega) hn) = 0 := by
  have hX := actual_native_numerator_triple_zero p n hp he
  have hc := X_pow_dvd_iff.mp hX
  have hA0 : (clearedNumerator (ZMod p) n).eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact hc 0 (by omega)
  have hA1 : (clearedNumerator (ZMod p) n).derivative.eval 0 = 0 := by
    rw [← taylor_coeff_one, taylor_zero]
    exact hc 1 (by omega)
  have hA2 : (taylor (0 : ZMod p) (clearedNumerator (ZMod p) n)).coeff 2 = 0 := by
    rw [taylor_zero]
    exact hc 2 (by omega)
  unfold integralParameterSecondJet
  rw [secondJetOver_map, clearedNumerator_map, clearedDenominator_map,
    integralNode_residue]
  simp only [secondJetOver, hA0, hA1, hA2, zero_mul, sub_zero, add_zero]

/-- The ordinary full K tail is zero only after the original e cutoff. -/
theorem actual_full_second_field_tail (p n : ℕ) [Fact p.Prime]
    (hp : 19 ≤ p) (hn : n < p) (he : p - 1 - p / 6 < n) :
    (nativeFullSecondJetCoefficient p n : ZMod p) = 0 := by
  rw [← integralFullSecondCoefficient_value p n (by omega) hn]
  change residueHom p (integralFullSecondCoefficient p n (by omega) hn) = 0
  rw [integralFullSecondCoefficient, map_mul, map_ofNat,
    integral_second_jet_tail_zero p n hp hn he, mul_zero]

end WPMomentPrecision.SecondCutoff
