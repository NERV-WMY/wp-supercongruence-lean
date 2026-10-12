import WPActualRankTwoFirstLift

open scoped BigOperators Polynomial
open Polynomial WPPIntegralReduction WPActualNativeParameter WPActualRankTwoParameter
  WPActualRankTwoGaussODE WPActualRankTwoLegendreField WPActualRankTwoFirstLift WPActualCMGauss
  WPActualNativeFirstJet WPActualNativeSecondJet WPActualRankTwoDividedDifference
  WPNativeParameterTaylor

namespace WPActualRankTwoFixedDegree

/-- The actual normalized fixed-degree Gegenbauer family in Gaussian coordinates. -/
noncomputable def fixedNumerator (K : Type*) [CommRing K] (d n : ℕ) : K[X] :=
  ∏ j ∈ Finset.range n, C ((j : K) - (d : K)) * (C ((d : K) + (j : K) + 1) + 2 * X)

noncomputable def fixedDenominator (K : Type*) [CommRing K] (n : ℕ) : K[X] :=
  ∏ j ∈ Finset.range n, C ((j : K) + 1) * (C ((j : K) + 1) + X)

theorem fixedNumerator_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (d n : ℕ) : (fixedNumerator K d n).map f = fixedNumerator L d n := by
  simp [fixedNumerator, Polynomial.map_prod]

theorem fixedDenominator_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (n : ℕ) : (fixedDenominator K n).map f = fixedDenominator L n := by
  simp [fixedDenominator, Polynomial.map_prod]

theorem fixedNumerator_eval_succ (K : Type*) [CommRing K] (d n : ℕ) (t : K) :
    (fixedNumerator K d (n + 1)).eval t = (fixedNumerator K d n).eval t *
      (((n : K) - (d : K)) * ((n : K) + (d : K) + 1 + 2 * t)) := by
  simp [fixedNumerator, Finset.prod_range_succ]
  ring

theorem fixedDenominator_eval_succ (K : Type*) [CommRing K] (n : ℕ) (t : K) :
    (fixedDenominator K (n + 1)).eval t = (fixedDenominator K n).eval t *
      (((n : K) + 1) * ((n : K) + 1 + t)) := by
  simp [fixedDenominator, Finset.prod_range_succ]

theorem fixedDenominator_eval_zero (K : Type*) [CommRing K] (n : ℕ) :
    (fixedDenominator K n).eval 0 = (n.factorial : K) ^ 2 := by
  induction n with
  | zero => simp [fixedDenominator]
  | succ n ih =>
    rw [fixedDenominator_eval_succ, ih, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem rankDenominator_fixed (K : Type*) [CommRing K] (n : ℕ) (t : K) :
    (rankDenominator K n).eval t = (36 : K) ^ n * (fixedDenominator K n).eval t := by
  induction n with
  | zero => simp [rankDenominator, fixedDenominator]
  | succ n ih =>
    rw [rankDenominator_eval_succ, fixedDenominator_eval_succ, ih, pow_succ]
    ring

theorem actual_low_fixed_factor (p j : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (6 * (j : ℚ) + 1 - (p : ℚ)) * (6 * (j : ℚ) + 5 - (p : ℚ)) =
      36 * ((j : ℚ) - ((p / 6 : ℕ) : ℚ)) *
        ((j : ℚ) + ((p / 6 : ℕ) : ℚ) + 1 - (p : ℚ) / 3) := by
  rcases prime_six_classes p hp with h1 | h5
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 1 := by exact_mod_cast h1
    rw [hq]
    ring
  · have hq : (p : ℚ) = 6 * ((p / 6 : ℕ) : ℚ) + 5 := by exact_mod_cast h5
    rw [hq]
    ring

/-- The literal low-node numerator is this fixed-degree family in both prime classes. -/
theorem actual_rankNumerator_fixed (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (rankNumerator ℚ n).eval (-(p : ℚ) / 6) =
      (36 : ℚ) ^ n * (fixedNumerator ℚ (p / 6) n).eval (-(p : ℚ) / 6) := by
  induction n with
  | zero => simp [rankNumerator, fixedNumerator]
  | succ n ih =>
    rw [rankNumerator_eval_succ, fixedNumerator_eval_succ, ih, pow_succ]
    linear_combination
      ((36 : ℚ) ^ n * (fixedNumerator ℚ (p / 6) n).eval (-(p : ℚ) / 6)) *
        actual_low_fixed_factor p n hp

noncomputable def fixedCoefficient (d n : ℕ) (t : ℚ) : ℚ :=
  (fixedNumerator ℚ d n).eval t / (fixedDenominator ℚ n).eval t

theorem actual_low_fixedCoefficient (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankCoefficient n (-(p : ℚ) / 6) = fixedCoefficient (p / 6) n (-(p : ℚ) / 6) := by
  rw [rankCoefficient, actual_rankNumerator_fixed p n hp, rankDenominator_fixed]
  unfold fixedCoefficient
  exact mul_div_mul_left _ _ (pow_ne_zero n (by norm_num : (36 : ℚ) ≠ 0))

theorem fixedCoefficient_origin_recurrence (d n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * fixedCoefficient d (n + 1) 0 =
      ((n : ℚ) - (d : ℚ)) * ((n : ℚ) + (d : ℚ) + 1) * fixedCoefficient d n 0 := by
  have hD : (fixedDenominator ℚ n).eval 0 ≠ 0 := by
    rw [fixedDenominator_eval_zero]
    positivity
  have hDnext : (fixedDenominator ℚ (n + 1)).eval 0 ≠ 0 := by
    rw [fixedDenominator_eval_zero]
    positivity
  rw [fixedDenominator_eval_succ] at hDnext
  have hB := (mul_ne_zero_iff.mp hDnext).2
  have hf (a u d b : ℚ) (hd : d ≠ 0) (hb : b ≠ 0) :
      b * (a * u / (d * b)) = u * (a / d) := by field_simp [hd, hb]
  unfold fixedCoefficient
  rw [fixedNumerator_eval_succ, fixedDenominator_eval_succ]
  convert hf ((fixedNumerator ℚ d n).eval 0)
    (((n : ℚ) - d) * ((n : ℚ) + d + 1 + 2 * 0))
    ((fixedDenominator ℚ n).eval 0)
    (((n : ℚ) + 1) * ((n : ℚ) + 1 + 0)) hD hB using 1 <;> ring

theorem fixedCoefficient_origin_legendre (d n : ℕ) :
    fixedCoefficient d n 0 = ((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff n := by
  induction n with
  | zero => simp [fixedCoefficient, fixedNumerator, fixedDenominator,
      Polynomial.coeff_map, coeff_shiftedLegendre]
  | succ n ih =>
    have hr := fixedCoefficient_origin_recurrence d n
    rw [ih] at hr
    have hl : ((n : ℚ) + 1) ^ 2 * ((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff (n + 1) =
        ((n : ℚ) - (d : ℚ)) * ((n : ℚ) + (d : ℚ) + 1) *
          ((shiftedLegendre d).map (Int.castRingHom ℚ)).coeff n := by
      simp only [Polynomial.coeff_map]
      have h := congrArg (Int.castRingHom ℚ) (shiftedLegendre_cleared_recurrence d n)
      simpa only [map_mul, map_pow, map_add, map_sub, map_natCast, map_one] using h
    apply mul_left_cancel₀ (pow_ne_zero 2 (by positivity : (n : ℚ) + 1 ≠ 0))
    linear_combination hr - hl

noncomputable def fixedPolynomial (d : ℕ) (t : ℚ) : ℚ[X] :=
  rankCoefficientPolynomial d (fun n => fixedCoefficient d n t)

theorem fixedPolynomial_origin_legendre (d : ℕ) :
    fixedPolynomial d 0 = (shiftedLegendre d).map (Int.castRingHom ℚ) := by
  ext n
  rw [fixedPolynomial, rankCoefficientPolynomial_coeff]
  split_ifs with hn
  · exact fixedCoefficient_origin_legendre d n
  · symm
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hd : ((shiftedLegendre d).map (Int.castRingHom ℚ)).natDegree ≤ d :=
      Polynomial.natDegree_map_le.trans (by rw [natDegree_shiftedLegendre])
    omega

theorem actual_low_fixedPolynomial (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    rankNodePolynomial p 1 = fixedPolynomial (p / 6) (-(p : ℚ) / 6) := by
  ext n
  rw [fixedPolynomial, rankCoefficientPolynomial_coeff]
  by_cases hn : n < p / 6 + 1
  · rw [if_pos hn, rankNodePolynomial, WPActualNativeSecondTaylor.coefficientPolynomial_coeff,
      if_pos (by omega)]
    simpa only [Nat.cast_one, neg_one_mul] using actual_low_fixedCoefficient p n hp
  · rw [if_neg hn]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((actual_low_rankNode_degree p hp).trans_lt (by omega))

theorem fixedDenominator_origin_residue_ne_zero (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : (fixedDenominator (ZMod p) n).eval 0 ≠ 0 := by
  have h := rankDenominator_origin_residue_ne_zero p n hp hn
  rw [rankDenominator_fixed] at h
  exact (mul_ne_zero_iff.mp h).2

theorem fixedDenominator_node_residue (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    residueHom p ((fixedDenominator (integralRationals p) n).eval (integralNode p hp)) =
      (fixedDenominator (ZMod p) n).eval 0 := by
  rw [← Polynomial.eval_map_apply, fixedDenominator_map, integralNode_residue]

theorem fixedDenominator_node_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((fixedDenominator (integralRationals p) n).eval (integralNode p hp)).val ≠ 0 ∧
      (((fixedDenominator (integralRationals p) n).eval (integralNode p hp)).val)⁻¹ ∈
        integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [fixedDenominator_node_residue]
  exact fixedDenominator_origin_residue_ne_zero p n hp hn

theorem fixedDenominator_origin_unit (p n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ((fixedDenominator (integralRationals p) n).eval 0).val ≠ 0 ∧
      (((fixedDenominator (integralRationals p) n).eval 0).val)⁻¹ ∈ integralRationals p := by
  apply integral_inverse_of_residue_ne_zero
  rw [← Polynomial.eval_map_apply, fixedDenominator_map, map_zero]
  exact fixedDenominator_origin_residue_ne_zero p n hp hn

noncomputable def fixedOriginInverse (p n : ℕ) [Fact p.Prime] (hp : 7 ≤ p) (hn : n < p) :
    integralRationals p :=
  ⟨((fixedDenominator (integralRationals p) n).eval 0).val⁻¹,
    (fixedDenominator_origin_unit p n hp hn).2⟩

noncomputable def fixedFirstOriginIntegral (p d n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) : integralRationals p :=
  firstJetOver (fixedNumerator (integralRationals p) d n)
    (fixedDenominator (integralRationals p) n) 0 (fixedOriginInverse p n hp hn)

theorem fixedFirstOriginIntegral_value (p d n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    (fixedFirstOriginIntegral p d n hp hn).val =
      WPNativeParameterTaylor.quotientJet (fixedNumerator ℚ d n) (fixedDenominator ℚ n) 0 := by
  have hD := (fixedDenominator_origin_unit p n hp hn).1
  rw [evaluate_subtype, fixedDenominator_map, Subring.coe_zero] at hD
  unfold fixedFirstOriginIntegral firstJetOver fixedOriginInverse
  change ((fixedNumerator (integralRationals p) d n).derivative.eval 0).val *
      (((fixedDenominator (integralRationals p) n).eval 0).val⁻¹) -
    ((fixedNumerator (integralRationals p) d n).eval 0).val *
      ((fixedDenominator (integralRationals p) n).derivative.eval 0).val *
      (((fixedDenominator (integralRationals p) n).eval 0).val⁻¹) ^ 2 = _
  rw [derivative_evaluate_subtype, derivative_evaluate_subtype]
  simp only [evaluate_subtype, fixedNumerator_map, fixedDenominator_map, Subring.coe_zero]
  simpa only [firstJetOver] using
    firstJetOver_rational (fixedNumerator ℚ d n) (fixedDenominator ℚ n) 0 hD

/-- The actual family Taylor expansion has a proved integral p^2 remainder. -/
theorem actual_fixedCoefficient_first_remainder (p d n : ℕ) [Fact p.Prime]
    (hp : 7 ≤ p) (hn : n < p) :
    ∃ r : integralRationals p,
      fixedCoefficient d n (-(p : ℚ) / 6) - fixedCoefficient d n 0 +
        (p : ℚ) / 6 * WPNativeParameterTaylor.quotientJet
          (fixedNumerator ℚ d n) (fixedDenominator ℚ n) 0 = (p : ℚ) ^ 2 * r.val / 36 := by
  let A := fixedNumerator (integralRationals p) d n
  let D := fixedDenominator (integralRationals p) n
  let t := integralNode p hp
  let u0 := fixedOriginInverse p n hp hn
  let ut : integralRationals p := ⟨(D.eval t).val⁻¹, (fixedDenominator_node_unit p n hp hn).2⟩
  let g := fixedFirstOriginIntegral p d n hp hn
  let k := secondJetOver A D 0 u0
  have h0 : D.eval 0 * u0 = 1 := by
    apply Subtype.ext
    change (D.eval 0).val * (D.eval 0).val⁻¹ = 1
    exact mul_inv_cancel₀ (fixedDenominator_origin_unit p n hp hn).1
  have ht : D.eval t * ut = 1 := by
    apply Subtype.ext
    change (D.eval t).val * (D.eval t).val⁻¹ = 1
    exact mul_inv_cancel₀ (fixedDenominator_node_unit p n hp hn).1
  obtain ⟨r, hr⟩ := integral_centred_second_expansion A D t u0 ut h0 ht
  have h := congrArg Subtype.val hr
  change (A.eval t).val / (D.eval t).val - (A.eval 0).val / (D.eval 0).val -
    t.val * g.val - t.val ^ 2 * k.val = t.val ^ 3 * r.val at h
  dsimp only [A, D, t] at h
  rw [evaluate_subtype, evaluate_subtype, evaluate_subtype, evaluate_subtype] at h
  simp only [fixedNumerator_map, fixedDenominator_map, integralNode_value, Subring.coe_zero] at h
  change fixedCoefficient d n (-(p : ℚ) / 6) - fixedCoefficient d n 0 -
    (-(p : ℚ) / 6) * g.val - (-(p : ℚ) / 6) ^ 2 * k.val =
      (-(p : ℚ) / 6) ^ 3 * r.val at h
  change fixedCoefficient d n (-(p : ℚ) / 6) - fixedCoefficient d n 0 -
    (-(p : ℚ) / 6) * (fixedFirstOriginIntegral p d n hp hn).val -
      (-(p : ℚ) / 6) ^ 2 * k.val = (-(p : ℚ) / 6) ^ 3 * r.val at h
  rw [fixedFirstOriginIntegral_value] at h
  let a6 : integralRationals p := ⟨1 / 6,
    WPFiniteConductorPolynomial.small_inverse_integral p 6 (by norm_num) (by omega)⟩
  refine ⟨k - (p : integralRationals p) * a6 * r, ?_⟩
  change fixedCoefficient d n (-(p : ℚ) / 6) - fixedCoefficient d n 0 +
      (p : ℚ) / 6 * WPNativeParameterTaylor.quotientJet
        (fixedNumerator ℚ d n) (fixedDenominator ℚ n) 0 =
    (p : ℚ) ^ 2 * (k.val - (p : ℚ) * (1 / 6 : ℚ) * r.val) / 36
  linear_combination h

end WPActualRankTwoFixedDegree
